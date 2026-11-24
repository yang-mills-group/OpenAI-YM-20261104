import YM.Integration.ActualScalarTransport
import YM.MergeProof.Bungalow
import YM.Overlay.Terminal

/-! Exact normalization and signed readout on one literal actual history.
The complete joint birth is independent of the later Freight/Fusion
representation estimates, so these equalities do not import those suppliers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG MeasureTheory Marker MergeProof MergeProof.Accent
open Push GridApprox.Nil Extra.Trajectories OPE.Therm
open scoped BigOperators

variable {G : Gauge} (C : Family G) {N p j k : ℕ}

section JointBirth
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The entire original array of insertions enters one common actual birth
and one common actual push. Products of separate conditional means do not
occur in this definition. -/
def actualJointBirth (Φ : I → Config G (C.side N p) → ℂ) (hj : j ≤ N) :
    Config G (C.side j p) → Poly (Stock.census I) :=
  gust C.path N p N (Accent.birth (Stock.census I) (C.path.rep N p N) Φ) j hj

end JointBirth

section Normalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Normalize a complete signed numerator at its actual birth level, then
transport it through the same fixed cutoff and period. -/
def actualSignedTransport (X : Config G (C.side j p) → E) (hk : k ≤ j) :
    Config G (C.side k p) → E :=
  actualTransport C (N := N)
    (fun U => ((C.path.rep N p j).eval U)⁻¹ • X U) hk

variable (hC : C.Makes)
include hC

theorem actualSignedTransport_eq (hj : j ≤ N)
    (X : Config G (C.side j p) → E) (hk : k ≤ j)
    (U : Config G (C.side k p)) :
    actualSignedTransport C (N := N) X hk U =
      ((C.path.rep N p k).eval U)⁻¹ • gust C.path N p j X k hk U := by
  have he : (fun V => (C.path.rep N p j).eval V •
      (((C.path.rep N p j).eval V)⁻¹ • X V)) = X := by
    funext V
    rw [smul_smul, mul_inv_cancel₀
      (Multi.AxisShift.chosen_positive hC.wilson hj V).ne', one_smul]
  unfold actualSignedTransport actualTransport
  rw [he]

theorem actualSignedTransport_unnormalize (hj : j ≤ N)
    (X : Config G (C.side j p) → E) (hk : k ≤ j)
    (U : Config G (C.side k p)) :
    (C.path.rep N p k).eval U • actualSignedTransport C (N := N) X hk U =
      gust C.path N p j X k hk U := by
  rw [actualSignedTransport_eq C hC hj, smul_smul, mul_inv_cancel₀
    (Multi.AxisShift.chosen_positive hC.wilson (hk.trans hj) U).ne', one_smul]

theorem actualSignedTransport_integrable (hj : j ≤ N)
    {X : Config G (C.side j p) → E} (hX : Integrable X (prior G _))
    (hk : k ≤ j) :
    Integrable (actualSignedTransport C (N := N) X hk) (scene C.path N p k) := by
  apply actualScene_integrable_of_weighted C hC (hk.trans hj)
  simp_rw [actualSignedTransport_unnormalize C hC hj]
  exact gust_live C.path N p j X hX hk

/-- Every readout level uses the original Wilson partition at cutoff `N`.
The signed numerator's mean is preserved, including all marked modes. -/
theorem actualSignedTransport_mean [CompleteSpace E] (hj : j ≤ N)
    {X : Config G (C.side j p) → E} (hX : Integrable X (prior G _))
    (hk : k ≤ j) :
    (∫ U, actualSignedTransport C (N := N) X hk U ∂scene C.path N p k) =
      (partition G (C.side N p) (C.path.β N p N))⁻¹ • ∫ U, X U ∂prior G _ := by
  rw [actualScene_formula C hC (hk.trans hj)]
  simp_rw [actualSignedTransport_unnormalize C hC hj]
  rw [gust_sum C.path N p j X hX hk]

end Normalization

section Coefficients
variable {V : Type} [Fintype V] [DecidableEq V] {B : Census V}
variable (hC : C.Makes)
include hC

omit [Fintype V] in
theorem actualSignedTransport_coefficient_mean (hj : j ≤ N)
    {X : Config G (C.side j p) → Poly B} (hX : Integrable X (prior G _))
    (hk : k ≤ j) (i : B.Mode) :
    (∫ U, (actualSignedTransport C (N := N) X hk U).part i
      ∂scene C.path N p k) =
      (partition G (C.side N p) (C.path.β N p N))⁻¹ •
        ∫ U, (X U).part i ∂prior G _ := by
  let L := (Poly.get i).restrictScalars ℝ
  change (∫ U, L (actualSignedTransport C (N := N) X hk U)
    ∂scene C.path N p k) = _
  rw [L.integral_comp_comm (actualSignedTransport_integrable C hC hj hX hk),
    actualSignedTransport_mean C hC hj hX hk, L.map_smul,
    ← L.integral_comp_comm hX]
  rfl

end Coefficients

end YM.Integration
