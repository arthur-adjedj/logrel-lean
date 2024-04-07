import Lake
open Lake DSL

package «logrel-lean» where
  -- add package configuration options here

lean_lib «LogrelLean» where
  -- add library configuration options here

@[default_target]
lean_exe «logrel-lean» where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "nightly-testing"

require aesop from git "https://github.com/JLimperg/aesop" @ "nightly-testing"
