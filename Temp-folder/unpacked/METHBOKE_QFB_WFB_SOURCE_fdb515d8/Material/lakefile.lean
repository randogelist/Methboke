import Lake
open Lake DSL

package material where
  version := v!"0.1.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

lean_lib SingularClosure where
  srcDir := "_vendor"
  globs := #[.submodules `SingularClosure]

lean_lib QuasiFeffermanB where
  srcDir := "_vendor"
  globs := #[.submodules `QuasiFeffermanB]

@[default_target]
lean_lib Galerkin where
  roots := #[`Galerkin.Endpoint]

@[default_target]
lean_lib MathlibAnalytic where
  roots := #[`MathlibAnalytic.Endpoint]

@[default_target]
lean_lib MathlibFourier where
  roots := #[`MathlibFourier.Endpoint]

@[default_target]
lean_lib MathlibODE where
  roots := #[`MathlibODE.Endpoint]

@[default_target]
lean_lib PhysicalNSE where
  roots := #[`PhysicalNSE.Endpoint]

@[default_target]
lean_lib QFBCutoff where
  roots := #[`QFBCutoff.Endpoint]

@[default_target]
lean_lib QFBLerayHopf where
  roots := #[`QFBLerayHopf.Endpoint]

@[default_target]
lean_lib QFBRestart where
  roots := #[`QFBRestart.Endpoint]

@[default_target]
lean_lib QFBRoot where
  roots := #[`QFBRoot.Endpoint]

@[default_target]
lean_lib QFBTail where
  roots := #[`QFBTail.Endpoint]

@[default_target]
lean_lib QFBTraceUniqueness where
  roots := #[`QFBTraceUniqueness.Endpoint]

@[default_target]
lean_lib RelativeEnergy where
  roots := #[`RelativeEnergy.Endpoint]

@[default_target]
lean_lib SerrinComparison where
  roots := #[`SerrinComparison.Endpoint]

@[default_target]
lean_lib SmallH12 where
  roots := #[`SmallH12.Endpoint]

