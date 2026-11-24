import YM.Integration.WilsonJointAxialScalar
import YM.Integration.WilsonReceivedCloseOrdinaryGrade

/-! One restoration of the actual weights on the signed ordinary observation.
The aperture order can be increased after fixing the stencil and the face
inverse. Its exceptional probability pays the full rough finite-degree bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonJointAxialCash
open Finset Marker Multi QuadraticLocal
open WilsonJointAxialHearing WilsonReceivedWholeFieldHot
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] (J : Census V)

private theorem fee (s : J.Mode) {g E : ℝ} (gp : 0 < g) (small : g ≤ 1)
    (a p : ℕ) (load : s.val.card ≤ a) (good : 0 ≤ E) (paid : E ≤ g^(p+1+a)) :
    feeFor s (p+1) g E ≤ WilsonReceivedCloseOrdinaryGrade.invoice J a 0 p 1*g^(p+1) := by
  apply WilsonReceivedCloseOrdinaryGrade.earned J s a 0 p le_rfl gp small gp
    (by linarith) (by linarith only [inv_pos.mpr gp]) load
  simp only [zero_mul,add_zero,pow_zero,one_mul,one_pow]
  unfold feeFor
  refine add_le_add ?_ le_rfl
  apply Finset.sum_le_sum
  intro h _
  exact mul_le_mul (mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg _))
    (pow_le_pow_left₀ (add_nonneg (inv_nonneg.mpr gp.le) good) (add_le_add le_rfl paid) _)
    (pow_nonneg (add_nonneg (inv_nonneg.mpr gp.le) good) _)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg gp.le _))

omit [Fintype V] in
private theorem hot (s : J.Mode) {g D C κ B : ℝ} (gp : 0 < g) (small : g ≤ 1)
    (a d p : ℕ) (load : s.val.card ≤ a) (hd : 0 ≤ D) (hc : 1 ≤ C) (hb : 0 ≤ B)
    (raw : D ≤ C/g^d) (rare : κ ≤ B*g^(p+d*a)) :
    κ*charge s D ≤ B*(Fintype.card (parts J).Mode)*C^a*g^p := by
  have grow : 1 ≤ C/g^d := (le_div_iff₀ (pow_pos gp _)).mpr (by
    rw [one_mul]; exact (pow_le_one₀ gp.le small).trans hc)
  have byTerm (h) (hS : h ∈ shards J s) :
      D^h.val.card ≤ (C/g^d)^a :=
    (pow_le_pow_left₀ hd raw _).trans (pow_le_pow_right₀ grow ((WilsonFiniteOrdinaryTail.blocks s h hS).trans load))
  have total : charge s D ≤ (Fintype.card (parts J).Mode : ℝ)*(C/g^d)^a := by
    refine (Finset.sum_le_sum byTerm).trans ?_
    rw [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ _)) (pow_nonneg (zero_le_one.trans grow) _)
  calc
    _ ≤ (B*g^(p+d*a))*((Fintype.card (parts J).Mode : ℝ)*(C/g^d)^a) :=
      mul_le_mul rare total (Finset.sum_nonneg fun _ _ => pow_nonneg hd _) (mul_nonneg hb (pow_nonneg gp.le _))
    _ = _ := by rw [pow_add,pow_mul,div_pow]; field_simp

theorem restored (S : Finset J.Mode) (c : J.Mode → ℂ) (w : J.Mode → ℝ)
    {g E D C κ B M : ℝ} (gp : 0 < g) (small : g ≤ 1) (a d p W : ℕ)
    (load : ∀ s ∈ S, s.val.card ≤ a) (weights : ∀ s ∈ S, 0 < w s)
    (income : g^W*(∑ s∈S,‖c s‖/w s) ≤ M)
    (eg : 0 ≤ E) (paid : E ≤ g^((p+W)+1+a))
    (hd : 0 ≤ D) (hc : 1 ≤ C) (hb : 0 ≤ B) (raw : D ≤ C/g^d)
    (rare : κ ≤ B*g^((p+W)+1+d*a)) :
    (∑ s∈S,‖c s‖*(feeFor s ((p+W)+1) g E / w s))+
        κ*(∑ s∈S,‖c s‖*(charge s D / w s)) ≤
      M*(WilsonReceivedCloseOrdinaryGrade.invoice J a 0 (p+W) 1 +
        B*(Fintype.card (parts J).Mode)*C^a)*g^(p+1) := by
  let total := WilsonReceivedCloseOrdinaryGrade.invoice J a 0 (p+W) 1+B*(Fintype.card (parts J).Mode)*C^a
  have nt : 0 ≤ total := add_nonneg (WilsonReceivedCloseOrdinaryGrade.nonneg J a 0 (p+W) zero_le_one)
    (mul_nonneg (mul_nonneg hb (Nat.cast_nonneg _)) (pow_nonneg (zero_le_one.trans hc) _))
  have per (s) (hs : s∈S) :
      feeFor s ((p+W)+1) g E + κ*charge s D ≤ total*g^((p+W)+1) := by
    rw [show total*g^((p+W)+1)=_ from add_mul _ _ _]
    exact add_le_add (fee J s gp small a (p+W) (load s hs) eg paid)
      (hot J s gp small a d ((p+W)+1) (load s hs) hd hc hb raw rare)
  calc
    _ = ∑ s∈S,(‖c s‖/w s)*(feeFor s ((p+W)+1) g E+κ*charge s D) := by
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s∈S,(‖c s‖/w s)*(total*g^((p+W)+1)) :=
      Finset.sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (per s hs) (div_nonneg (norm_nonneg _) (weights s hs).le)
    _ = (g^W*(∑ s∈S,‖c s‖/w s))*total*g^(p+1) := by
      rw [← Finset.sum_mul,show p+W+1=W+(p+1) by omega,pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right income nt) (pow_nonneg gp.le _)

end YM.Integration.WilsonJointAxialCash
