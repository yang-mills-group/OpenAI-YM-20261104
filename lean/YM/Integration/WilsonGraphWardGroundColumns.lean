import YM.Integration.WilsonGraphGroupGroundMultilinear
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentGroupFirstWardTree

/-! Finite Maxwell columns on the occupied support of a signed Ward test. -/
noncomputable section
namespace YM.Integration.WilsonGraphWardGroundColumns
open _root_.YangMills _root_.YangMills.Matching MeasureTheory
open _root_.YM.Integration.WilsonGraphGroupGroundMultilinear (labels firstSlotAdd firstSlotSMul)
open scoped Classical BigOperators
variable (g : GaugeGroup)
variable (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) {n : ℕ}
variable (d : Fin (n + 1) → ℕ) (v : (i : Fin (n + 1)) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))

def point (g : GaugeGroup) (S : Conversion (_root_.IssuedMaxwell.Reports.B g)) {n : ℕ}
    (d : Fin (n + 1) → ℕ) (v : (i : Fin (n + 1)) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (a : (_root_.IssuedMaxwell.Reports.B g).sector (d 0)) (x : Points (n + 1)) : ℂ :=
  S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0
    (labels g d (Function.update v 0 a)) x

private def momentLinear (g : GaugeGroup) {n : ℕ}
    (d : Fin (n + 1) → ℕ) (v : (i : Fin (n + 1)) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (x : Points (n + 1)) (hx : x ∈ separated (n + 1)) :
    (_root_.IssuedMaxwell.Reports.B g).sector (d 0) →ₗ[ℂ] ℂ where
  toFun a := (_root_.IssuedMaxwell.Reports.B g).moment x (fun i => (Function.update v 0 a i).val)
  map_add' a b := firstSlotAdd g d x hx v a b
  map_smul' c a := firstSlotSMul g d x hx v c a

private theorem atMoment (x : Points (n + 1)) (hx : x ∈ separated (n + 1))
    (a : (_root_.IssuedMaxwell.Reports.B g).sector (d 0)) : point g S d v a x = momentLinear g d v x hx a :=
  _root_.PhysicalMatching.H7IndependentGroupFirstWardTree.groupLeading S
    (labels g d (Function.update v 0 a)) x hx

theorem finiteFirst (x : Points (n + 1)) (hx : x ∈ separated (n + 1))
    {m : ℕ} (u : Fin m → ℂ) (columns : Fin m → (_root_.IssuedMaxwell.Reports.B g).sector (d 0)) :
    point g S d v (∑ i, u i • columns i) x =
      ∑ i, u i * point g S d v (columns i) x := by
  classical
  simp only [atMoment g S d v x hx, map_sum, map_smul, smul_eq_mul]

theorem integrated {X : Type*} [MeasureSpace X] (shape : X → Points (n + 1))
    (weight : X → ℂ)
    (occupied : ∀ z, weight z ≠ 0 → shape z ∈ separated (n + 1))
    {m : ℕ} (u w : Fin m → ℂ) (columns : Fin m → (_root_.IssuedMaxwell.Reports.B g).sector (d 0))
    (paid : ∀ i, Integrable (fun z => weight z * point g S d v (columns i) (shape z))) :
    (∫ z, weight z * (point g S d v (∑ i, u i • columns i) (shape z) -
      point g S d v (∑ i, w i • columns i) (shape z))) =
      ∑ i, (u i - w i) * ∫ z, weight z * point g S d v (columns i) (shape z) := by
  classical
  have pointwise (z : X) :
      weight z * (point g S d v (∑ i, u i • columns i) (shape z) -
        point g S d v (∑ i, w i • columns i) (shape z)) =
        ∑ i, (u i - w i) * (weight z * point g S d v (columns i) (shape z)) := by
    by_cases h : weight z = 0
    · simp [h]
    · rw [finiteFirst g S d v (shape z) (occupied z h) u columns,
          finiteFirst g S d v (shape z) (occupied z h) w columns,
          ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
  calc
    _ = ∫ z, ∑ i, (u i - w i) * (weight z * point g S d v (columns i) (shape z)) :=
      integral_congr_ae (Filter.Eventually.of_forall pointwise)
    _ = ∑ i, ∫ z, (u i - w i) * (weight z * point g S d v (columns i) (shape z)) :=
      integral_finsetSum Finset.univ (fun i _ => (paid i).const_mul (u i - w i))
    _ = _ := Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)

end YM.Integration.WilsonGraphWardGroundColumns
end

