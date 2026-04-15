import Lake
open Lake DSL

private def pkgConfig (pkg : String) (mode : String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #[mode, pkg] }
  if out.exitCode == 0 then
    return out.stdout.trimAscii.toString.splitOn " " |>.filter (· != "") |>.toArray
  return #[]

package «type-driven-dev» where
  version := v!"0.1.0"

require hale from git
  "https://github.com/typednotes/hale.git" @ "v0.3.1"

lean_lib TypeDrivenDev

lean_exe «type-driven-dev» where
  root := `Main
  moreLinkArgs := run_io (pkgConfig "openssl" "--libs")

lean_exe «tensor-search» where
  root := `TypeDrivenDev.TensorSearch
