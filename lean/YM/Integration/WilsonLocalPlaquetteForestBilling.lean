import YM.Integration.WilsonLocalPlaquetteForest
import YM.Integration.WilsonLocalPlaquetteBonds

/-! Summing the exact changed-bond tariff directly over the freely
charted physical forest wires leaves no unselected-volume factor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteForestBilling
open Finset Lattice RG Tree Wilson WilsonLocalPlaquetteForest WilsonLocalPlaquetteAction
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f}

theorem amount (T:Forest S.ratio) (E:Finset T.Free) (k:ℕ) (X Y:↥E→G.Color) :
    load (k+1) (support T E) (extend T E X 0) (extend T E Y 0)≤
      6*∑i:↥E,(‖X i‖^(k+1)+‖Y i‖^(k+1)) := by
  apply (WilsonLocalPlaquetteBonds.original k (support T E) (extend T E X 0) (extend T E Y 0)).trans_eq
  congr 1
  let h (i:Edge (Site f)):=‖extend T E X 0 i‖^(k+1)+‖extend T E Y 0 i‖^(k+1)
  change (∑i∈support T E,h i)=_
  rw [support,Finset.sum_image (fun a _ b _ he=>Subtype.ext he),←Finset.sum_attach E (fun a:T.Free=>h a.val)]
  apply Finset.sum_congr Finset.attach_eq_univ
  intro i _
  simp [h,extend,i.val.property,i.property]

theorem uniform {ι:Type} [Fintype ι] (k:ℕ) (X Y:ι→G.Color) (A:ℝ) (cost:∀i,‖X i‖≤A ∧ ‖Y i‖≤A) :
    (∑i:ι,(‖X i‖^k+‖Y i‖^k)) ≤ (Fintype.card ι:ℝ)*(2*A^k) := by
  calc
    _≤∑i:ι,(A^k+A^k) := Finset.sum_le_sum (fun i _=>add_le_add (pow_le_pow_left₀ (norm_nonneg _) (cost i).1 _)
      (pow_le_pow_left₀ (norm_nonneg _) (cost i).2 _))
    _=_ := by simp only [sum_const,card_univ,nsmul_eq_mul];ring

end YM.Integration.WilsonLocalPlaquetteForestBilling
