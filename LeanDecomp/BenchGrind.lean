import LeanDecomp.bigstep

open LeanDecomp.BigStepTest

set_option profiler true

namespace LeanDecomp.BenchGrind

theorem bench_if_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t -> (S, s) ==> t := by
  grind [BigStep]

end LeanDecomp.BenchGrind
