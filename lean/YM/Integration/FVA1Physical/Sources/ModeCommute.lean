import YM.Integration.FVA1Physical.Sources.TerminalMoment

/-! A fixed mode test commutes pointwise with every stage of actual blocking. -/

namespace YM.Integration.FVA1Physical

open Filter MeasureTheory Wilson RG MergeProof.Accent

theorem gust_modeTest_eq {I : Type*} [DecidableEq I] {B : Marker.Census I}
    {G : Gauge} (H : History G) (N n : ℕ)
    (seed : Config G (H.S.side N n) → Marker.Poly B)
    (hseed : Integrable seed (prior G (H.S.side N n))) (u : B.Mode → ℂ)
    (i : ℕ) (hi : i ≤ N) :
    (fun v => modeTest u (gust H N n N seed i hi v)) =
      gust H N n N (fun v => modeTest u (seed v)) i hi := by
  let L := (modeFunctional u).restrictScalars ℝ
  induction hi using Nat.decreasingInduction with
  | self => rw [gust_base, gust_base]
  | of_succ k hk ih =>
    rw [gust_step H N n N seed hk, gust_step H N n N _ hk, ← ih]
    funext v
    unfold StepData.push
    have hi := StepData.push_slice (H.levels.transition_mass k n (H.β N n (k+1))) v
      (gust H N n N seed (k+1) hk) (gust_live H N n N seed hseed hk)
    exact (L.integral_comp_comm hi).symm.trans (integral_congr_ae (Eventually.of_forall
      fun w => L.map_smul _ _))

end YM.Integration.FVA1Physical
