import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.AnalyticFree
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedMaxwell.AnalyticMoments
open YM YM.Maxwell YM.Maxwell.Wick YM.Maxwell.Wick.Occ Filter Set Function
open scoped ContDiff Topology BigOperators
variable {G:Gauge} {n:ℕ}

theorem entryAt (p q : Slot G) {x : E4 × E4} (h : x.1 ≠ x.2) :
    ContDiffAt ℝ ω (fun z : E4 × E4 => entry p q z.1 z.2) x  := by
  have hw : ContDiffAt ℝ ω (fun y : E4 × E4 => y.1-y.2) x := contDiffAt_fst.sub contDiffAt_snd
  have he := (AnalyticFree.original (coordinateLeg p) (coordinateLeg q) (sub_ne_zero.mpr h)).comp x hw
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x he

theorem monomialAt (W : Powers G n) {x : Points n} (hx : x ∈ conf n) :
    ContDiffAt ℝ ω (fun x => monomial x W) x := by
  classical
  unfold monomial
  apply ContDiffAt.sum
  intro P _
  unfold Occ.graph
  refine contDiffAt_prod ?_
  intro a ha
  have hs (i : Fin n) : ContDiffAt ℝ ω (fun y : Points n => y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ => E4) i).contDiff.contDiffAt
  have he := (entryAt a.probe ((partner P a).probe) (x := (x a.label, x (partner P a).label)) (show x a.label ≠ x (partner P a).label from
    (show Injective x.ofLp from hx).ne (different P a).symm)).comp x
      ((hs a.label).prodMk (hs (partner P a).label))
  exact he

theorem original (v : Fin n → WickPol G) {x : Points n} (hx : x ∈ conf n) :
    ContDiffAt ℝ ω (fun y => moment G y v) x := by
  simp_rw [sumFormula]
  exact ContDiffAt.sum fun _ _ => contDiffAt_const.mul (monomialAt _ hx)

end IssuedMaxwell.AnalyticMoments
end
