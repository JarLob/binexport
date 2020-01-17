// Copyright 2011-2020 Google LLC
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

#ifndef READER_READER_TEST_UTIL_H_
#define READER_READER_TEST_UTIL_H_

#include "third_party/absl/strings/string_view.h"
#include "third_party/zynamics/binexport/binexport2.pb.h"
#include "third_party/zynamics/binexport/util/status.h"

namespace security::binexport {

// Reads a BinExport2 proto from the testdata directory. The filename is
// relative to that directory.
not_absl::Status GetBinExportProtoForTesting(absl::string_view filename,
                                             BinExport2* proto);

}  // namespace security::binexport

#endif  // READER_READER_TEST_UTIL_H_
