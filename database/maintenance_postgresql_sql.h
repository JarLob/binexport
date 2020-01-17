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

#ifndef DATABASE_MAINTENANCE_POSTGRESQL_SQL_H_
#define DATABASE_MAINTENANCE_POSTGRESQL_SQL_H_

#include "third_party/absl/strings/string_view.h"

inline absl::string_view GetPostgreSqlMaintenance() {
  static constexpr char kPostgreSqlMaintenance[] = R"raw(
VACUUM ANALYZE "ex_?_operands";
VACUUM ANALYZE "ex_?_functions";
VACUUM ANALYZE "ex_?_basic_blocks";
VACUUM ANALYZE "ex_?_instructions";
VACUUM ANALYZE "ex_?_basic_block_instructions";
VACUUM ANALYZE "ex_?_callgraph";
VACUUM ANALYZE "ex_?_control_flow_graphs";
VACUUM ANALYZE "ex_?_expression_trees";
VACUUM ANALYZE "ex_?_expression_nodes";
VACUUM ANALYZE "ex_?_expression_tree_nodes";
VACUUM ANALYZE "ex_?_expression_substitutions";
VACUUM ANALYZE "ex_?_address_references";
VACUUM ANALYZE "ex_?_address_comments";
VACUUM ANALYZE "ex_?_type_renderers";
VACUUM ANALYZE "ex_?_base_types";
VACUUM ANALYZE "ex_?_types";
VACUUM ANALYZE "ex_?_expression_types";
VACUUM ANALYZE "ex_?_sections";
)raw";
  return kPostgreSqlMaintenance;
}

#endif  // DATABASE_MAINTENANCE_POSTGRESQL_SQL_H_
