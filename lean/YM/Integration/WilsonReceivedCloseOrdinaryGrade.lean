import YM.Integration.WilsonFiniteOrdinaryWindow
import YM.Integration.WilsonReceivedCloseFaceBudget

/-! Coupling powers for the complete partition sum of an enrolled finite source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseOrdinaryGrade

open Finset Marker Multi
open scoped BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] (J : Census V)

/-- The finite combinatorial fee is fixed before the physical cutoff and period. -/
def invoice (a d q : ℕ) (U : ℝ) : ℝ :=
  U^a * (Fintype.card (parts J).Mode : ℝ) * ((a:ℝ)*4^a+3^(q+d*a+1))

omit [Fintype V] in
theorem nonneg (a d q : ℕ) {U : ℝ} (hu : 0 ≤ U) : 0 ≤ invoice J a d q U := by
  unfold invoice
  positivity

private theorem cutoff {g t : ℝ} (gp : 0<g) (cold : g≤1) (tp : 0<t)
    (edge : t⁻¹ ≤ 3*g⁻¹) (a u n : ℕ) (load : n ≤ a) :
    (n:ℝ)*g^(u+a)*(t⁻¹+g^(u+a))^n ≤ ((a:ℝ)*4^a)*g^u := by
  have inv : 1 ≤ g⁻¹ := one_le_inv_iff₀.mpr ⟨gp,cold⟩
  have small := pow_le_one₀ gp.le cold (n:=u+a)
  have grow : 1 ≤ 4*g⁻¹ := by linarith only [inv]
  have sum : t⁻¹+g^(u+a) ≤ 4*g⁻¹ := by linarith only [small,edge,inv]
  have high := (pow_le_pow_left₀ (add_nonneg (inv_nonneg.mpr tp.le) (pow_nonneg gp.le _)) sum n).trans
    (pow_le_pow_right₀ grow load)
  calc
    _ ≤ (a:ℝ)*g^(u+a)*(4*g⁻¹)^a := mul_le_mul
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr load) (pow_nonneg gp.le _)) high (by positivity) (by positivity)
    _ = _ := by rw [pow_add,mul_pow,inv_pow]; field_simp

omit [Fintype V] in
/-- Each disjoint connected block spends at most one coupling power. The original inverse
source radius is restored once for each occupied name after the partition sum. -/
theorem earned (s : J.Mode) (a d q : ℕ) {U g t value : ℝ} (unit : 1 ≤ U)
    (gp : 0<g) (cold : g≤1) (tp : 0<t) (edge : t≤3*g) (inverse : t⁻¹≤3*g⁻¹)
    (occupied : s.val.card ≤ a)
    (purchased : value ≤ (U*(g⁻¹)^d)^s.val.card *
      ((∑ h∈shards J s, (h.val.card:ℝ)*g^(q+d*a+1+a)*(t⁻¹+g^(q+d*a+1+a))^h.val.card) +
        t^(q+d*a+1)*(shards J s).card)) :
    value ≤ invoice J a d q U * g^(q+1) := by
  let u := q+d*a+1
  have inv : 1 ≤ g⁻¹ := one_le_inv_iff₀.mpr ⟨gp,cold⟩
  have upper : (U*(g⁻¹)^d)^s.val.card ≤ (U*(g⁻¹)^d)^a := pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le unit (one_le_pow₀ inv)) occupied
  have nn := (zero_le_one.trans unit)
  have pieces : (∑ h∈shards J s, (h.val.card:ℝ)*g^(u+a)*(t⁻¹+g^(u+a))^h.val.card) ≤
      ((shards J s).card:ℝ)*(((a:ℝ)*4^a)*g^u) := by
    calc
      _ ≤ ∑ _h∈shards J s, ((a:ℝ)*4^a)*g^u := Finset.sum_le_sum fun h hh =>
        cutoff gp cold tp inverse a u h.val.card ((WilsonFiniteOrdinaryTail.blocks s h hh).trans occupied)
      _ = _ := by simp
  have power : t^u ≤ 3^u*g^u := (pow_le_pow_left₀ tp.le edge u).trans_eq (mul_pow ..)
  have shardBound : ((shards J s).card:ℝ) ≤ Fintype.card (parts J).Mode :=
    Nat.cast_le.mpr (Finset.card_le_univ _)
  have full : (∑ h∈shards J s, (h.val.card:ℝ)*g^(u+a)*(t⁻¹+g^(u+a))^h.val.card) +
      t^u*(shards J s).card ≤ (Fintype.card (parts J).Mode:ℝ)*((a:ℝ)*4^a+3^u)*g^u := by
    calc
      _ ≤ (shards J s).card*(((a:ℝ)*4^a)*g^u)+(3^u*g^u)*(shards J s).card :=
        add_le_add pieces (mul_le_mul_of_nonneg_right power (Nat.cast_nonneg _))
      _ = ((shards J s).card:ℝ)*((a:ℝ)*4^a+3^u)*g^u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right shardBound (by positivity)) (pow_nonneg gp.le _)
  have unwind : (g⁻¹)^(d*a)*g^u = g^(q+1) := by
    rw [show u=d*a+(q+1) by dsimp only [u]; omega,pow_add,inv_pow,←mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ gp.ne'),one_mul]
  apply purchased.trans
  calc
    _ ≤ (U*g⁻¹^d)^s.val.card * ((Fintype.card (parts J).Mode:ℝ)*((a:ℝ)*4^a+3^u)*g^u) :=
      mul_le_mul_of_nonneg_left full (by positivity)
    _ ≤ (U*g⁻¹^d)^a * ((Fintype.card (parts J).Mode:ℝ)*((a:ℝ)*4^a+3^u)*g^u) :=
      mul_le_mul_of_nonneg_right upper (by positivity)
    _ = _ := by
      rw [mul_pow,←pow_mul]
      calc _ = (U^a * (Fintype.card (parts J).Mode:ℝ) * ((a:ℝ)*4^a+3^u))*((g⁻¹)^(d*a)*g^u) := by ring
           _ = _ := by rw [unwind]; rfl

end YM.Integration.WilsonReceivedCloseOrdinaryGrade
