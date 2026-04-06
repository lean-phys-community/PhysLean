import Lake
open System Lake DSL

package «Physlib»

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.28.0"

@[default_target]
lean_lib Physlib where
  moreLeanArgs := #[
    "-Dwarn.sorry=false"
  ]

@[default_target]
lean_lib QuantumInfo where
  moreLeanArgs := #[
    "-Dwarn.sorry=false"
  ]

-- These were their own lean_lib in Lean-QuantumInfo, we should move them to appropriate directories.
-- lean_lib ClassicalInfo
-- lean_lib StatMech

lean_exe check_file_imports where
  srcDir := "scripts"

lean_exe style_lint where
  srcDir := "scripts/MetaPrograms"

lean_exe type_former_lint where
  srcDir := "scripts"

lean_exe lint_all where
  supportInterpreter := true
  srcDir := "scripts"

lean_exe check_dup_tags where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

lean_exe sorry_lint where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

lean_exe runPhyslibLinters where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

-- Other linting scripts

lean_exe free_simps where
  srcDir := "scripts/MetaPrograms"

lean_exe spelling where
  srcDir := "scripts/MetaPrograms"

lean_exe check_rfl where
  srcDir := "scripts/MetaPrograms"

lean_exe redundant_imports where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

lean_exe module_doc_lint where
  srcDir := "scripts/MetaPrograms"

-- Stats

lean_exe stats where
  supportInterpreter := true
  srcDir := "scripts"

lean_exe local_stats where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

-- Scripts for the website

lean_exe make_tag where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

lean_exe TODO_to_yml where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

lean_exe informal where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

-- Old

lean_exe find_TODOs where
  srcDir := "scripts"

lean_exe notes where
  supportInterpreter := true
  srcDir := "scripts/MetaPrograms"

lean_exe mathlib_textLint_on_physlib where
  srcDir := "scripts"

lean_exe no_docs where
  srcDir := "scripts/MetaPrograms"

-- Optional scripts

-- Optional inclusion of llm. Needed for `openAI_doc_check`
-- require llm from git "https://github.com/leanprover-community/llm" @ "main"

-- Optional inclusion of tryAtEachStep
-- require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "main"

-- Optional inclusion of LeanCopilot
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.4.1"

-- lean_exe commands defined specifically for Physlib.

-- Optional inclusion of openAI_doc_check. Needs `llm` above.
-- lean_exe openAI_doc_check where
--   srcDir := "scripts"
