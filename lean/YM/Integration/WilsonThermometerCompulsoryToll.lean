import YM.Integration.WilsonThermometerCompulsoryReturn

/-! Restore the actual reporting incidence after the genuine older Wilson posterior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerCompulsoryToll
open FVA1 Finset Function MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter OriginalForcedAddresses
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
open WilsonThermometerCourseHearing
open OPE.Therm
variable {G : Gauge} (R : Run G) {N i per : ℕ}

private theorem scaled (hi : i ≤ N) (a : ℝ) (f : Config G (R.family.side i per) → ℂ)
    {u : ℕ} (old : u ≤ i) :
    actualTransport R.family (N:=N) (fun W => a • f W) old =
      fun U => a • actualTransport R.family (N:=N) f old U := by
  induction old using Nat.decreasingInduction with
  | self => simp only [actualTransport_base R.family R.makes hi]
  | of_succ j hj ih =>
    funext U
    simp only [actualTransport_step R.family R.makes hi _ hj,ih,actualAverage]
    simp_rw [smul_comm (actualConditionalDensity R.family N per j U _) a]
    exact integral_smul _ _

private theorem scale (hi : i ≤ N) (a : ℝ) (pos : 0 ≤ a)
    {f : Config G (R.family.side i per) → ℂ} {price : ℝ}
    (receipt : WilsonThermometerCompulsoryReturn.Heard R (top:=N) f price) :
    WilsonThermometerCompulsoryReturn.Heard R (top:=N) (fun F => a • f F) (a*price) := by
  intro u old
  have due := receipt u old
  dsimp only at due ⊢
  rw [scaled R hi a f old]
  refine ⟨fun F => ?_,fun Y hY => ?_⟩
  · rw [norm_smul,Real.norm_of_nonneg pos]
    exact mul_le_mul_of_nonneg_left (due.1 F) pos
  · have h := due.2 Y hY
    simp_rw [mul_smul_comm]
    refine ⟨h.1.smul a,?_⟩
    rw [integral_smul,norm_smul,Real.norm_of_nonneg pos]
    exact (mul_le_mul_of_nonneg_left h.2 pos).trans_eq (by ring)

/-- The original top test wallet and Filed radius pay one inverse weight per
occupied physical leg, also after arbitrary earlier integrations. -/
theorem original (hi : i ≤ N) {V : Type} [DecidableEq V] {S : Marker.Census V} (s : S.Mode)
    {first now : V → ℝ} {E Ω h : ℝ} (price : 0 ≤ E) (sale : 0 < Ω) (radius : 0 < h)
    (top : Poly.toll first s*(E*Ω)^s.val.card=1)
    (next : ∀ v, now v=first v/(Ω^6*h))
    {f : Config G (R.family.side i per) → ℂ} {cost : ℝ}
    (receipt : WilsonThermometerCompulsoryReturn.Heard R (top:=N) (fun F => Poly.toll now s • f F) cost) :
    WilsonThermometerCompulsoryReturn.Heard R (top:=N) f ((E*Ω^7*h)^s.val.card*cost) := by
  have tickets : Poly.toll now s*(Ω^6*h)^s.val.card=Poly.toll first s := by
    unfold Poly.toll
    rw [prod_congr rfl (fun v _ => next v),prod_div_distrib,prod_const]
    field_simp
  have exactToll : (E*Ω^7*h)^s.val.card*Poly.toll now s=1 := by
    rw [show E*Ω^7*h=(E*Ω)*(Ω^6*h) by ring,mul_pow]
    calc _ = (Poly.toll now s*(Ω^6*h)^s.val.card)*(E*Ω)^s.val.card := by ring
         _ = 1 := by rw [tickets,top]
  have proof := scale R hi ((E*Ω^7*h)^s.val.card) (by positivity) receipt
  simpa only [smul_smul,exactToll,one_smul] using proof

end YM.Integration.WilsonThermometerCompulsoryToll
end
