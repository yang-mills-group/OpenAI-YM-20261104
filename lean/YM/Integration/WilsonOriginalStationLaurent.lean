import YM.Integration.WilsonOriginalStarSceneRent
import YM.Integration.WilsonPositionThermometerStationNorm

/-! One ante-regulator wallet for all original inverse-fitted cutoff legs on a
reporting mesh. Every term is issued on their actual common Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStationLaurent
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonOriginalStarSceneRent
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {I T : Type} [Fintype I] [DecidableEq I]
  {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
  {D : ℕ} (j : I → Fin (D+1)) (M : I→ℝ)

def mass := ∑i, WilsonPositionThermometerStationNorm.cost R.family (j i) * max 0 (M i)
omit [DecidableEq I] in
private theorem component (i : I) :
    WilsonPositionThermometerStationNorm.cost R.family (j i) * M i ≤ mass R j M := by
  have pos (a : I) : 0 ≤ WilsonPositionThermometerStationNorm.cost R.family (j a):=by
    unfold WilsonPositionThermometerStationNorm.cost
    positivity
  exact (mul_le_mul_of_nonneg_left (le_max_right ..) (pos i)).trans
    (single_le_sum (f:=fun a=>WilsonPositionThermometerStationNorm.cost R.family (j a)*max 0 (M a))
      (fun a _=>mul_nonneg (pos a) (le_max_left ..)) (mem_univ i))

def fields (W : Vane R.family D) (u : ∀ i,(Bel R.family.book).Field (j i)) (k N p : ℕ)
    (i : I) : R.family.label (j i) :=
  Price.awake R.family (j i) k N p (W.wheel.atCut (N,p) (j i) (u i))

omit [DecidableEq I] in
theorem bound (simple : G.Simple) (ε : ℝ) (eps : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (W : Vane R.family D), W.k=k → W.checked f H D →
    ∀ (u : ∀i,(Bel R.family.book).Field (j i)), (∀i,‖u i‖ ≤ M i) → ∀ (N p : ℕ), k<N →
      ∀ i, (R.family.labels.level (j i)).coeffSize (fields R j W u k N p i) ≤
        (R.family.path.levels.clock.hatBeta k)^ε * mass R j M := by
  filter_upwards [eventually_all.mpr fun i:I=>WilsonPositionThermometerStationNorm.original
    (f:=f) (H:=H) simple R.makes (j i) ε eps,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0] with k paid pos W date checked u limits N p top i
  have amount:=paid i W (j i) rfl date checked (u i) N p top
  refine amount.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg pos _))
  have pCost : 0 ≤ WilsonPositionThermometerStationNorm.cost R.family (j i):=by
    unfold WilsonPositionThermometerStationNorm.cost
    positivity
  exact (mul_le_mul_of_nonneg_left (limits i) pCost).trans (component R j M i)

theorem original (simple : G.Simple) (ε : ℝ) (eps : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (σ Ω:ℝ), 1 ≤ Ω →
      let d:=fun i=>(j i).val
      let K:=(R.family.path.levels.clock.hatBeta k)^ε * mass R j M
      let E:=max 1 ((1+K)*wallet R d σ)
      let w:=fun _ : I=>(E*Ω)⁻¹
      ∀ (W : Vane R.family D), W.k=k → W.checked f H D →
      ∀ (u : ∀i,(Bel R.family.book).Field (j i)), (∀i,‖u i‖ ≤ M i) → ∀ (N p : ℕ), k<N →
      ∀ (o : I → Site (R.family.side k p)) (t : I → T → ℂ), (∀i x,‖t i x‖ ≤ 1) →
      let g:=Pert.Asymptotics.regulatorRun R.family N p k
      let X:=rows R d o σ g (R.family.path.rep N p k).p.threshold (fields R j W u k N p) t
      ∀ (order count stage vac coarse : ℕ), Fintype.card I ≤ count → maximum R d ≤ order → order+1 ≤ stage →
      order ≤ coarse → tariff R d ≤ coarse → order+Fintype.card I*tariff R d ≤ AllOrder.Burn.horizon vac+2 →
      Scene.Armada X w (fun _=>tariff R d) σ Ω⁻¹ order count (Fintype.card I*tariff R d) ∧
        Mentor.Cruise.Voter X σ order count stage vac coarse ∧
        ∀ A:(Stock.census I).Mode, Poly.toll w A*(E*Ω)^A.val.card=1 := by
  filter_upwards [bound R j M (f:=f) (H:=H) simple ε eps,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0] with k paid pos σ Ω one d K E w W date checked u limits N p top o t ht g X order count stage vac coarse load fit room future stamp cover
  have cap:=paid W date checked u limits N p top
  have masspos : 0 ≤ mass R j M:=by
    have charge (i : I) : 0 ≤ WilsonPositionThermometerStationNorm.cost R.family (j i) := by
      unfold WilsonPositionThermometerStationNorm.cost
      positivity
    exact sum_nonneg fun i _=>mul_nonneg (charge i) (le_max_left ..)
  have band : g ≤ 2*(R.family.path.rep N p k).p.threshold:=by
    have budgetHere : (R.family.path.rep N p k).p = R.family.path.levels.budget k :=
      (R.makes.wilson.represents N p k top.le).vac
    rw [budgetHere]
    exact (RG04B.thresholdHat R.makes (p:=p) top.le).2
  exact appointed R d o σ g _ _ t (mul_nonneg (Real.rpow_nonneg pos _) masspos) cap
    (ActualRunKernelPackets.regulator_pos R N p k top.le).le (R.family.path.rep N p k).p.threshold_pos band one ht
    order count stage vac coarse load fit room future stamp cover

end YM.Integration.WilsonOriginalStationLaurent
