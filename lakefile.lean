import Lake
open Lake DSL

package «lean-decomp» where
  -- additional configuration options can go here

@[default_target]
lean_lib «LeanDecomp» where
  -- additional configuration options can go here

/-- Entry point for `lake exe lean-decomp`. -/
@[default_target]
lean_exe «lean-decomp» where
  root := `LeanDecomp.Main

/-- Test library — built by default so CI catches test failures. -/
@[default_target]
lean_lib «LeanDecompTest» where
  globs := #[.one `LeanDecomp.Test, .one `LeanDecomp.bigstep, .one `LeanDecomp.simple]
