// Copyright 2011-2019 Google LLC. All Rights Reserved.
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

#include "third_party/zynamics/binexport/binaryninja/log_handler.h"

// clang-format off
#include "binaryninjaapi.h"  // NOLINT
// clang-format on

#include "third_party/zynamics/binexport/util/logging.h"

namespace security::binexport {

void BinaryNinjaLogHandler(LogLevel level, const char* filename, int line,
                           const std::string& message) {
  LogLine(level, filename, line, message);
  BNLogLevel bn_level;
  switch (level) {
    case LogLevel::LOGLEVEL_INFO:
      bn_level = InfoLog;
      break;
    case LogLevel::LOGLEVEL_WARNING:
      bn_level = WarningLog;
      break;
    case LogLevel::LOGLEVEL_ERROR:
    case LogLevel::LOGLEVEL_FATAL:
    default:
      bn_level = ErrorLog;
      break;
  }
  BinaryNinja::Log(bn_level, "%s", message.c_str());
}

}  // namespace security::binexport