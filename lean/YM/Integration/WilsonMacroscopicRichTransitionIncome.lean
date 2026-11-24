import YM.Integration.WilsonMacroscopicRichSparseTransition
import YM.Integration.WilsonMacroscopicRichNormalizedRows

/-! Pay the derivatives of the genuine complete transition and its pushed vacuum on the same finite set of varied lower bonds. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichTransitionIncome
open Function Filter MeasureTheory Set Lattice Wilson RG Source Push.Local Push.Local.Kernel PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichSparseTransition WilsonMacroscopicRichNormalizedRows
open scoped Classical BigOperators Topology
variable {G : Gauge} {c f : Side}

def Born (J : Edges c) (r : ℝ) (A : Directions G c) : Prop := Supported J A ∧ ∀ i∈J, ‖A i‖ ≤ r

theorem negative {J : Edges c} {r : ℝ} {A : Directions G c} (ha : Born J r A) : Born J r (-A) := by
  exact ⟨fun i hi => by change -(A i) = 0; rw [ha.1 i hi,neg_zero],fun i hi => (norm_neg (A i)).le.trans (ha.2 i hi)⟩

theorem assigned (S : StepData c f) (β : ℝ) (U : Config G f) :
    (fun V => S.density β U V) = mixture S U ∘ noiseLift S β Finset.univ := by
  funext V; rw [Function.comp_apply,evaluated]
  change (∑ t,S.likelihood U t * S.noise β (S.prediction U t) V) = ∑ t,S.likelihood U t * noiseLift S β Finset.univ V (S.prediction U t)
  simp_rw [lifted]; rfl

theorem point (S : StepData c f) (β : ℝ) (U : Config G f) (l : List (Directions G c)) (V : Config G c) :
    leftDerivs (fun W => S.density β U W) l V = weights S U (fun Q => leftDerivs (noisy S β Finset.univ Q) l V) := by
  have hd := smooth_lift S β Finset.univ V l.length
  have he (Q : Config G c) : leftDerivs (noisy S β Finset.univ Q) l V = leftDerivs (noiseLift S β Finset.univ) l V Q := by
    let L : C(Config G c,ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ Q
    rw [show noisy S β Finset.univ Q = L ∘ noiseLift S β Finset.univ from funext fun v => (lifted ..).symm,left_linear L l hd le_rfl]; rfl
  rw [assigned,left_linear _ _ hd le_rfl,evaluated,funext he]

theorem numerator (S : StepData c f) (β : ℝ) (J : Edges c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (U : Config G f) (V : Config G c) (l : List (Directions G c)) (hk : l.length ≤ k) (ha : ∀ A∈l,Born J r A) :
    ‖leftDerivs (fun W => S.density β U W) l V‖ ≤ (noiseFactor G (β*S.kernel.penalty) k J.card r)^k * S.density β U V := by
  rw [point]; exact WilsonMacroscopicRichSparseTransition.bound S β J U V k hr l hk (fun A hA => (ha A hA).1) (fun A hA => (ha A hA).2)

theorem denominator (S : StepData c f) (hS : S.patch.Branches S.kernel G) (β : ℝ) (J : Edges c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (D : Config G f → ℝ) (hD : Integrable D (prior G f)) (pos : ∀ U, 0 ≤ D U)
    (V : Config G c) (l : List (Directions G c)) (hk : l.length ≤ k) (ha : ∀ A∈l,Born J r A) :
    ‖leftDerivs (S.push β D) l V‖ ≤ (noiseFactor G (β*S.kernel.penalty) k J.card r)^k * S.push β D V := by
  let C := (noiseFactor G (β*S.kernel.penalty) k J.card r)^k
  have incoming := slice_int S hS hD (noiseLift S β Finset.univ V)
  have value : (fun U => weights S U (noiseLift S β Finset.univ V) • D U) = (fun U => S.density β U V * D U) := by
    funext U
    change weights S U (noiseLift S β Finset.univ V) * D U = _
    rw [← evaluated]; exact congrArg (· * D U) (congrFun (assigned S β U) V).symm
  rw [value] at incoming
  change ‖leftDerivs (pass S β Finset.univ D) l V‖ ≤ C * ∫ U, S.density β U V * D U ∂prior G f
  rw [left_pass S β Finset.univ hS hD V l, ←integral_const_mul]
  apply norm_integral_le_of_norm_le (incoming.const_mul C) (.of_forall ?_)
  intro U
  have row := WilsonMacroscopicRichSparseTransition.bound S β J U V k hr l hk (fun A hA => (ha A hA).1) (fun A hA => (ha A hA).2)
  simpa only [smul_eq_mul,norm_mul,Real.norm_of_nonneg (pos U),mul_assoc] using mul_le_mul_of_nonneg_right row (pos U)

end YM.Integration.WilsonMacroscopicRichTransitionIncome
