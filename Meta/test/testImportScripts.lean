
def main (_ : List String) : IO Unit := do

  -- test alphaFileImports
  let alphaFileImportTest ← IO.Process.output {cmd := "lake", args := #["exe", "alphaFileImports", 
    "./Meta/test/test_project/TestProject", "./Meta/test/test_project/TestProject.lean"]}
  let expectedStr := "Error: The following .lean files are not imported in ./Meta/test/test_project/TestProject.lean:\n  - public import Meta.test.test_project.TestProject.Dir2.Advanced\n"

  if alphaFileImportTest.stdout == expectedStr
    then do IO.println "alphaFileImports works as intended!"
    else do IO.println s!"Error: alphaFileImports output is not what is expected:\n-------\n{alphaFileImportTest.stdout}"

  -- test noAlphaImports
  let noAlphaImportsTest ← IO.Process.output {cmd := "lake", args := #["exe", "noAlphaImports", "./Meta/test/test_project/TestProject"]}

  let expectedStr := "Found Violations:\n  ./Meta/test/test_project/TestProject/Dir1/Advanced.lean : PhyslibAlpha.ClassicalFieldTheory.Local.Action\n"

  if noAlphaImportsTest.stdout == expectedStr
    then do IO.println "noAlphaImports works as intended"
    else do IO.println s!"Error: noAlphaImports output is not what is expected:\n----\n{noAlphaImportsTest.stdout}"

  return 
