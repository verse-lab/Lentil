import Lentil.Main

open Lean

namespace TLA

/-- `tla_merge_always t1, t2, ..., tn => h` performs `tla_merge_always' t1, t2, ..., tn => h`
    and then simplifies the result using `rw [← always_and] at h`.
    So the result would look like `h : e |=tla= □ (p1 ∧ p2 ∧ ... ∧ pn)`. -/
macro "tla_merge_always" tmss:term,+ "=>" h:ident : tactic => do
  `(tactic| ((tla_merge_always' $tmss,* => $h) ; (repeat rw [← always_and] at $h:ident)))

end TLA
