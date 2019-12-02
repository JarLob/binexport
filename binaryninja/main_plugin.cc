// Copyright 2019 Google LLC. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include "third_party/zynamics/binexport/binaryninja/main_plugin.h"

#include <iostream>//DBG!!!
#include <cstdint>
#include <string>

#include "base/logging.h"
#include "openssl/sha.h"
#include "third_party/absl/strings/escaping.h"
#include "third_party/absl/strings/match.h"
#include "third_party/absl/strings/str_cat.h"
#include "third_party/absl/strings/str_format.h"
#include "third_party/zynamics/binexport/binaryninja/log_handler.h"
#include "third_party/zynamics/binexport/binexport2_writer.h"
#include "third_party/zynamics/binexport/call_graph.h"
#include "third_party/zynamics/binexport/entry_point.h"
#include "third_party/zynamics/binexport/flow_graph.h"
#include "third_party/zynamics/binexport/instruction.h"
#include "third_party/zynamics/binexport/util/canonical_errors.h"
#include "third_party/zynamics/binexport/util/filesystem.h"
#include "third_party/zynamics/binexport/util/format.h"
#include "third_party/zynamics/binexport/util/logging.h"
#include "third_party/zynamics/binexport/util/status_macros.h"
#include "third_party/zynamics/binexport/util/statusor.h"
#include "third_party/zynamics/binexport/util/timer.h"
#include "third_party/zynamics/binexport/version.h"

namespace security::binexport {

not_absl::StatusOr<std::string> GetInputFileSha256(
    BinaryNinja::BinaryView* view) {
  auto raw_view = view->GetParentView();
  if (!raw_view) {
    return not_absl::InternalError("Failed to load SHA256 hash of input file");
  }
  BinaryNinja::DataBuffer buffer =
      raw_view->ReadBuffer(0, raw_view->GetLength());

  std::string sha256_hash(32, '\0');
  SHA256_CTX sha256_ctx;
  SHA256_Init(&sha256_ctx);

  constexpr size_t kBufSize = 4096;
  const size_t buf_len = buffer.GetLength();
  for (size_t off = 0; off < buf_len; off += kBufSize) {
    SHA256_Update(&sha256_ctx,
                  reinterpret_cast<const char*>(buffer.GetDataAt(off)),
                  std::min(buf_len - off, kBufSize));
  }

  SHA256_Final(reinterpret_cast<unsigned char*>(&sha256_hash[0]), &sha256_ctx);
  return absl::BytesToHexString(sha256_hash);
}

std::string GetArchitectureName(BinaryNinja::BinaryView* view) {
  auto default_arch = view->GetDefaultArchitecture();
  std::string name = default_arch->GetName();
  std::string architecture;
  if (absl::StartsWith(name, "x86")) {
    architecture = "x86";
  } else if (absl::StartsWith(name, "arm") || name == "aarch64") {
    architecture = "ARM";
  } else if (absl::StartsWith(name, "mips")) {
    architecture = "MIPS";
  } else if (name == "ppc64") {
    architecture = "PowerPC";
  } else {
    architecture = "GENERIC";
  }

  if (default_arch->GetAddressSize() == 8) {
    absl::StrAppend(&architecture, "-64");
  } else if (default_arch->GetAddressSize() == 4) {
    absl::StrAppend(&architecture, "-32");
  }
  return architecture;
}

int GetArchitectureBitness(BinaryNinja::BinaryView* view) {
  return view->GetDefaultArchitecture()->GetAddressSize() * 8;
}

template <typename T>
T GetBytes(BinaryNinja::BinaryView* view, uint64_t start, size_t length) {
  BinaryNinja::DataBuffer buffer = view->ReadBuffer(start, length);
  const size_t bytes_read = buffer.GetLength();

  LOG_IF(ERROR, bytes_read != length) << absl::StrFormat(
      "Expected %d bytes at %08X, got %d", length, start, bytes_read);

  auto* data = reinterpret_cast<typename T::value_type*>(buffer.GetData());
  return T(data, data + bytes_read);
}

std::string GetBytes(BinaryNinja::BinaryView* view,
                     const Instruction& instruction) {
  return "";
}

std::vector<Byte> GetSectionBytes(BinaryNinja::BinaryView* view, uint64_t start,
                                  size_t length) {
  return GetBytes<std::vector<Byte>>(view, start, length);
}

int GetPermissions(BinaryNinja::BinaryView* view,
                   const BinaryNinja::Section& section) {
  auto segment = view->GetSegmentAt(section.GetStart());
  CHECK(segment);

  int segment_flags = segment->GetFlags();
  int permissions = 0;
  if (segment_flags & SegmentDenyExecute) {
    permissions |= AddressSpace::kExecute;
  }
  if (segment_flags & SegmentWritable) {
    permissions |= AddressSpace::kWrite;
  }
  if (segment_flags & SegmentReadable) {
    permissions |= AddressSpace::kRead;
  }
  return permissions;
}

void AnalyzeFlowBinaryNinja(BinaryNinja::BinaryView* view,
                            EntryPoints* entry_points, Writer* writer,
                            detego::Instructions* instructions,
                            FlowGraph* flow_graph, CallGraph* call_graph) {
  Timer<> timer;
  AddressReferences address_references;

  // Add initial entry points as functions.
  for (const auto& entry_point : *entry_points) {
    if ((entry_point.IsFunctionPrologue() || entry_point.IsExternal() ||
         entry_point.IsCallTarget())) {
      call_graph->AddFunction(entry_point.address_);
    }
  }

  AddressSpace address_space;
  AddressSpace flags;
  for (auto section_ref : view->GetSections()) {
    const uint64_t section_start = section_ref->GetStart();
    const size_t section_length = section_ref->GetLength();
    const int section_permissions = GetPermissions(view, *section_ref);
    address_space.AddMemoryBlock(
        section_start, GetSectionBytes(view, section_start, section_length),
        section_permissions);
    flags.AddMemoryBlock(section_start,
                         AddressSpace::MemoryBlock(section_length),
                         section_permissions);
  }

  Instruction::SetBitness(GetArchitectureBitness(view));
  Instruction::SetGetBytesCallback([view](const Instruction& instruction) {
    return GetBytes(view, instruction);
  });
  Instruction::SetMemoryFlags(&flags);

  LOG(INFO) << "flow analysis";
  auto default_arch = view->GetDefaultArchitecture();
  const size_t max_instr_len = default_arch->GetMaxInstructionLength();
  for (EntryPointAdder entry_point_adder(entry_points, "flow analysis");
       !entry_points->empty();) {
    const Address address = entry_points->back().address_;
    entry_points->pop_back();

    if (flags[address] & FLAG_VISITED) {
      continue;
    }
    flags[address] |= FLAG_VISITED;

    auto instr_bytes =
        GetBytes<std::vector<Byte>>(view, address, max_instr_len);

    BinaryNinja::InstructionInfo binja_instruction;
    if (!default_arch->GetInstructionInfo(&instr_bytes[0], address,
                                          max_instr_len, binja_instruction)) {
      continue;
    }

    std::vector<BinaryNinja::InstructionTextToken> binja_tokens;
    size_t instr_len = binja_instruction.length;
    if (!default_arch->GetInstructionText(&instr_bytes[0], address, instr_len,
                                          binja_tokens)) {
      continue;
    }
    std::string c;
    for (const auto& t : binja_tokens) {
      c.append(t.text).append("|");
    }
    std::cerr << "xxx " << std::hex << address << " " << c << std::endl;
  }

  //////////////////////////
  const auto processing_time = absl::Seconds(timer.elapsed());
  timer.restart();

  LOG(INFO) << "writing...";
  auto ignore_error(writer->Write(*call_graph, *flow_graph, *instructions,
                                  address_references, /*type_system=*/nullptr,
                                  address_space));

  Operand::EmptyCache();
  Expression::EmptyCache();

  const auto writing_time = absl::Seconds(timer.elapsed());
  LOG(INFO) << absl::StrCat(view->GetFile()->GetOriginalFilename(), ": ",
                            HumanReadableDuration(processing_time),
                            " processing, ",
                            HumanReadableDuration(writing_time), " writing");
}

not_absl::Status ExportBinaryView(BinaryNinja::BinaryView* view,
                                  Writer* writer) {
  const std::string filename = view->GetFile()->GetOriginalFilename();
  LOG(INFO) << filename << ": starting export";
  Timer<> timer;
  EntryPoints entry_points;

  {
    EntryPointAdder function_adder(&entry_points, "functions");
    EntryPointAdder call_adder(&entry_points, "calls");
    for (auto func_ref : view->GetAnalysisFunctionList()) {
      auto symbol_ref = func_ref->GetSymbol();
      switch (symbol_ref->GetType()) {
        case FunctionSymbol:
          function_adder.Add(symbol_ref->GetAddress(),
                             EntryPoint::Source::FUNCTION_PROLOGUE);
          break;
        case ImportedFunctionSymbol:
          call_adder.Add(symbol_ref->GetAddress(),
                         EntryPoint::Source::CALL_TARGET);
          break;
        default:
          LOG(WARNING) << symbol_ref->GetShortName()
                       << " has unimplemented type " << symbol_ref->GetType();
      }
    }
  }

  Instructions instructions;
  FlowGraph flow_graph;
  CallGraph call_graph;
  AnalyzeFlowBinaryNinja(view, &entry_points, writer, &instructions,
                         &flow_graph, &call_graph);

  LOG(INFO) << absl::StrCat(
      filename, ": exported ", flow_graph.GetFunctions().size(),
      " functions with ", instructions.size(), " instructions in ",
      HumanReadableDuration(timer.elapsed()));
  return not_absl::OkStatus();
}

not_absl::Status ExportBinary(const std::string& filename,
                              BinaryNinja::BinaryView* view) {
  NA_ASSIGN_OR_RETURN(std::string sha256_hash, GetInputFileSha256(view));

  BinExport2Writer writer(filename, view->GetFile()->GetOriginalFilename(),
                          sha256_hash, GetArchitectureName(view));
  NA_RETURN_IF_ERROR(ExportBinaryView(view, &writer));
  return not_absl::OkStatus();
}

void Plugin::Run(BinaryNinja::BinaryView* view) {
  LOG(INFO) << "Plugin::Run()";
  const std::string filename =
      ReplaceFileExtension(view->GetFile()->GetFilename(), ".BinExport2");
  if (auto status = ExportBinary(filename, view); !status.ok()) {
    LOG(ERROR) << "Error exporting: " << std::string(status.error_message());
  }
}

bool Plugin::Init() {
  if (auto status = InitLogging(LoggingOptions{}, &BinaryNinjaLogHandler);
      !status.ok()) {
    BinaryNinja::LogError(
        "Error initializing logging, skipping BinExport plugin: %s",
        std::string(status.error_message()).c_str());
    return false;
  }

  LOG(INFO) << kBinExportName << " " << kBinExportDetailedVersion << ", "
            << kBinExportCopyright;

  BinaryNinja::PluginCommand::Register(
      kBinExportName, kDescription,
      [](BinaryNinja::BinaryView* view) { Plugin::instance()->Run(view); });

  return true;
}

}  // namespace security::binexport

extern "C" BINARYNINJAPLUGIN bool CorePluginInit() {
  return security::binexport::Plugin::instance()->Init();
}