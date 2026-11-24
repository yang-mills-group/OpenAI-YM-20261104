import YM.Integration.FVA1Physical.Sources.TestedFields
import YM.MergeProof.South.Window

/-! Extraction of constant mode tests from the pushed terminal marker polynomial. -/

namespace YM.Integration.FVA1Physical

open Filter MeasureTheory Lattice RG Wilson MergeProof.Accent
open scoped BigOperators

variable {I : Type*} [DecidableEq I] {B : Marker.Census I}

noncomputable def modeFunctional (u : B.Mode → ℂ) : Marker.Poly B →L[ℂ] ℂ where
  toFun := modeTest u
  map_add' X Y := by simp [modeTest, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    change (∑ m, u m * (c * X.part m)) = c * ∑ m, u m * X.part m
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => mul_left_comm _ _ _
  cont := continuous_finsetSum _ fun m _ => continuous_const.mul (Marker.Poly.part_cont m)

/-- A fixed joint-mode test of the whole transported density has the same
Haar integral as its fine terminal reading. -/
theorem terminal_modeTest_conservation {G : Gauge} (H : History G) (N n i : ℕ)
    (hi : i ≤ N) (seed : Config G (H.S.side N n) → Marker.Poly B)
    (hseed : Integrable seed (prior G (H.S.side N n))) (u : B.Mode → ℂ) :
    (∫ v, modeTest u (gust H N n N seed i hi v) ∂prior G (H.S.side i n)) =
      ∫ v, modeTest u (seed v) ∂prior G (H.S.side N n) := by
  let L := (modeFunctional u).restrictScalars ℝ
  calc
    _ = L (∫ v, gust H N n N seed i hi v ∂prior G (H.S.side i n)) :=
      L.integral_comp_comm (gust_live H N n N seed hseed hi)
    _ = L (∫ v, seed v ∂prior G (H.S.side N n)) :=
      congrArg L (gust_sum H N n N seed hseed hi)
    _ = _ := (L.integral_comp_comm hseed).symm

/-- Identify the unbounded exceptional contribution explicitly in a total
reading. The fine observable can replace the first integral using conservation. -/
theorem readout_away_from_exception {V : Type*} [MeasurableSpace V] (μ : Measure V)
    {good : Set V} (hs : MeasurableSet good) (actual forecast : V → ℂ)
    (ha : Integrable actual μ)
    (hd : IntegrableOn (fun v => actual v - forecast v) good μ)
    (Z : ℂ) (ε : ℝ)
    (h : ‖(∫ v in good, actual v - forecast v ∂μ) / Z‖ ≤ ε) :
    ‖((∫ v, actual v ∂μ) - (∫ v in goodᶜ, actual v ∂μ) -
      (∫ v in good, forecast v ∂μ)) / Z‖ ≤ ε := by
  have hf : IntegrableOn forecast good μ :=
    (ha.restrict.sub hd).congr (Eventually.of_forall fun v => sub_sub_cancel (actual v) (forecast v))
  rw [← integral_add_compl hs ha, add_sub_cancel_right, ← integral_sub ha.restrict hf]
  exact h

end YM.Integration.FVA1Physical
