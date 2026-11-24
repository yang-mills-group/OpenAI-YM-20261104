import YM.Integration.WilsonEmittedRootCensus
import YM.QuadraticLocal.Earn.Blend

/-! Every true emitted path is paid before its external field test. The
unchanged earned width gives the all-derivative joint bill at an original
root, with exponential decay beyond its chosen length cut. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedRootSalary
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums Comparison.Density
open WilsonEmittedWordJointFare
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (w : V→ℝ) (grades : V→ℕ) {σ b a g K θ : ℝ} {p pieces depth : ℕ}
variable (old : Armada M w grades σ b p pieces depth)
variable (B : BudgetPoint) (scope : Invoice.Supports B K a g σ θ)

def fee (G : Gauge) (j s : ℕ) :=
  (1+Render.couple j)^(s+1) * (1+Render.couple j * Render.pass G j)^s

theorem fee_pos (G : Gauge) (j s : ℕ) : 0 < fee G j s := by
  have h := Render.code_nn j
  have h' := Render.pass_nn G j
  unfold fee; positivity

private theorem row (T : Row P Γ G X) {σ : ℝ} (hσ : 0 ≤ σ)
    (grace : T.Graceful σ) {j s : ℕ} (hr : T.lamp.r ≤ s) (hs : T.lamp.stamp ≤ s) :
    fare T T.lamp.power j ≤ fee G j s * (1+(T.length:ℝ))^(j*s) := by
  let C := Render.couple j
  let H := Render.pass G j
  have hC : 0 ≤ C := Render.code_nn j
  have hH : 0 ≤ H := Render.pass_nn G j
  have hM : 0 ≤ T.atom.magnitude := Invoice.p_bound _ _
  have M1 : T.atom.magnitude ≤ 1 := by
    apply le_trans _ grace
    exact le_mul_of_one_le_right hM (Real.one_le_exp (mul_nonneg hσ (Nat.cast_nonneg _)))
  have hs' : power T T.lamp.power = T.lamp.stamp := by
    unfold power QuadraticLocal.Sunrise.Loan.stamp QuadraticLocal.Sunrise.Loan.power; omega
  have h₀ : C^(T.lamp.stamp+1) ≤ (1+C)^(s+1) := by
    exact (pow_le_pow_left₀ hC (le_add_of_nonneg_left zero_le_one) _).trans
      (pow_le_pow_right₀ (by linarith) (by omega))
  have h₁ : (C*H)^T.lamp.r ≤ (1+C*H)^s := by
    exact (pow_le_pow_left₀ (mul_nonneg hC hH) (le_add_of_nonneg_left zero_le_one) _).trans
      (pow_le_pow_right₀ (by have := mul_nonneg hC hH; linarith) hr)
  have h₂ : (1+(T.atom.length:ℝ))^(j*T.lamp.r) ≤ (1+(T.length:ℝ))^(j*s) := by
    have z : T.atom.length ≤ T.length := Nat.le_add_left .. 
    exact (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left z 1) _).trans
      (pow_le_pow_right₀ (by have := Nat.cast_nonneg (α:=ℝ) T.length; linarith)
        (Nat.mul_le_mul_left j hr))
  unfold fare Render.fareAt Render.entry fee
  rw [hs']
  change C*C^T.lamp.stamp*(T.atom.magnitude*(C*H)^T.lamp.r*(1+(T.atom.length:ℝ))^(j*T.lamp.r)) ≤ _
  have half := mul_le_mul h₀ h₁ (pow_nonneg (mul_nonneg hC hH) _) (by positivity)
  have cut := mul_le_mul half h₂ (by positivity) (by positivity)
  have pay := mul_le_mul_of_nonneg_right M1 (show 0 ≤ C^(T.lamp.stamp+1)*(C*H)^T.lamp.r*
    (1+(T.atom.length:ℝ))^(j*T.lamp.r) by positivity)
  calc _ = T.atom.magnitude * (C^(T.lamp.stamp+1)*(C*H)^T.lamp.r*
          (1+(T.atom.length:ℝ))^(j*T.lamp.r)) := by rw [pow_succ]; ring
       _ ≤ _ := (pay.trans_eq (one_mul _)).trans cut

def rent (x : X) (j : ℕ) (i : ι) :=
  Poly.toll w (M i).mode * (‖(M i).paint x‖ * fare (M i) (M i).lamp.power j)

include scope old in
theorem tail (x : X) (j m : ℕ) (o : Site n) :
    SumBudget (fun i => if m ≤ (M i).length then
      if o ∈ (M i).ground B then rent M w x j i * Real.exp (a*coverNumber B.B ((M i).ground B))
      else 0 else 0)
      (Footprint.payment 1 (B.B+2) (j*(p+depth+1)) θ (fee G j (p+depth+1)) b a
        (Invoice.tax (p+depth+1) pieces) * Real.exp (-θ)^m) := by
  let s := p+depth+1
  let φ i := Poly.toll w (M i).mode * (M i).salary
  let l i := (M i).length
  let z i := (M i).center
  let Xs i := (M i).ground B
  have hφ i : 0 ≤ φ i := mul_nonneg (Poly.worth old.positive _).le (M i).sound.le
  have hz : Footprint.Anchored z φ l σ b := by
    intro i
    convert old.suggests i using 1
    ext v
    unfold φ
    split
    · unfold Row.height l; ring
    · rfl
  have hr i := Armada.degreeR grades old.toMinistry (M i) (old.purchases.usable i)
  have pp i : 0 ≤ rent M w x j i := by
    have h := (tested (M i) (M i).lamp.power j (0:Chart G n) (by simp)).nonneg
    exact mul_nonneg (Poly.worth old.positive _).le (mul_nonneg (norm_nonneg _) h)
  have bound i : rent M w x j i ≤ fee G j s * φ i * (1+(l i:ℝ))^(j*s) := by
    obtain ⟨he,ht,hR⟩ := hr i
    have hst : (M i).lamp.stamp ≤ s := by unfold QuadraticLocal.Sunrise.Loan.stamp s; omega
    have h := row (M i) scope.2.2.2.2.1 (old.purchases.spend i) hR hst (j:=j)
    have hu := mul_le_mul (old.honor i x) h
      (tested (M i) (M i).lamp.power j (0:Chart G n) (by simp)).nonneg (M i).sound.le
    exact (mul_le_mul_of_nonneg_left hu (Poly.worth old.positive _).le).trans_eq (by unfold φ l; ring)
  apply Footprint.assigned_tail (id : Site n → Site n) 1 (fun i => by simp) z φ hφ l Xs hz
    (B.B+2) (j*s) B.B (v:=Invoice.tax s pieces) _ _ (fee_pos G j s).le scope.2.2.2.2.2
    (rent M w x j) pp bound m o
  · intro i y hy
    rw [id_eq,separation_comm]
    exact ((M i).near B.B y hy).trans (by unfold Row.radius l; nlinarith)
  · intro i
    have hb : 0 < (B.B:ℝ) := Nat.cast_pos.mpr B.B_pos
    have tiles : B.B*coverNumber B.B (Xs i) ≤ (1000+s+pieces)*B.B + l i :=
      ((M i).tiles B.B B.B_pos).trans (by unfold s; gcongr <;> first | exact (hr i).2.2 | apply old.quota)
    unfold Invoice.tax
    field_simp
    rw [Nat.mul_comm B.B] at tiles
    exact_mod_cast tiles

end YM.Integration.WilsonEmittedRootSalary
