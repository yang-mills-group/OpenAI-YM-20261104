import YM.Integration.WilsonEmittedCompactTariff
import YM.Integration.WilsonEmittedFiledCatalogue

/-! Charge a complete group-field catalogue before its finite summation over marked roots. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedJoinedFares
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.RG02 WilsonEmittedCompactTariff WilsonEmittedLocatedCensus
open scoped BigOperators
variable {V A:Type} [Fintype A] [DecidableEq V] {Γ:Census V}
variable (G:Gauge) (B:BudgetPoint) (s:Γ.Mode) (w:A→V→ℝ) (c:A→ℝ) (shift:A→ℕ)
variable (p pieces depth:A→ℕ) (b α σ:A→ℝ)

def cash := ∑ u:A, |c u| *((Poly.toll (w u) s)⁻¹*b u)

private theorem linearFee (J d:ℕ) (x:ℝ) : WilsonEmittedTransitionJet.fee J d x =
    WilsonEmittedTransitionJet.fee J d 1*x := by unfold WilsonEmittedTransitionJet.fee;ring

private theorem positiveFee (J d:ℕ) : 0≤WilsonEmittedTransitionJet.fee J d 1 := by
  unfold WilsonEmittedTransitionJet.fee Comparison.Density.Render.couple
  positivity

theorem original {J k m:ℕ} {x C τ:ℝ} (hh:1≤1+Real.log x) (hτ:0≤τ)
    (square:B.B=Nat.ceil ((Real.log x)^2))
    (cost:∀u, |WilsonEmittedTransitionJet.fee J (shift u) (fixed G J (p u+depth u+1) (pieces u))|≤C)
    (hs:∀u,p u+depth u+1≤k) (price:∀u,0<Poly.toll (w u) s)
    (old:∀u,0≤b u ∧ α u≤102 ∧ 0<σ u ∧ Real.exp (((σ u)⁻¹)^2)≤x)
    (tail:∀u, Real.exp (-strip (σ u))^m≤τ) :
    WilsonEmittedFiledCatalogue.rent (G:=G) w c shift B (p:=p) (pieces:=pieces) (depth:=depth)
        (b:=b) (α:=α) (θ:=fun u=>strip (σ u)) s J m ≤
      cash s w c b*C*(1+Real.log x)^(13+J*k)*τ := by
  classical
  set y:=1+Real.log x
  let t (u:A):=(Poly.toll (w u) s)⁻¹
  have hp (u:A):0≤t u:=inv_nonneg.mpr (price u).le
  have coef (u:A):0≤WilsonEmittedTransitionJet.fee J (shift u) 1:=positiveFee _ _
  unfold WilsonEmittedFiledCatalogue.rent cash
  rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro u _
  let d:=p u+depth u+1
  have base:=WilsonEmittedCompactTariff.original (G:=G) J d (pieces u)
    (old u).1 (old u).2.2.1 (old u).2.1 (old u).2.2.2 square
  have keep:=pow_le_pow_right₀ hh (show 13+J*d≤13+J*k by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left J (hs u)) _)
  have hf :0≤fixed G J d (pieces u):=by
    have money:0≤WilsonEmittedRootSalary.fee G J d:=(WilsonEmittedRootSalary.fee_pos ..).le
    unfold fixed;positivity
  have hbase:=base.trans (mul_le_mul_of_nonneg_left keep (mul_nonneg (old u).1 hf))
  have hm : receipt G B J d (pieces u) m (b u) (α u) (strip (σ u)) =
      receipt G B J d (pieces u) 0 (b u) (α u) (strip (σ u)) * Real.exp (-strip (σ u))^m := by
    unfold receipt; simp only [pow_zero,mul_one]
  have hraw := mul_le_mul hbase (tail u) (pow_nonneg (Real.exp_pos _).le _)
    (mul_nonneg (mul_nonneg (old u).1 hf)
      (pow_nonneg (zero_le_one.trans hh) _))
  rw [←hm] at hraw
  have paid := (le_abs_self _).trans (cost u)
  rw [linearFee] at paid
  rw [linearFee]
  calc
    _ ≤ |c u| *(WilsonEmittedTransitionJet.fee J (shift u) 1*
        (t u*(b u*fixed G J d (pieces u)*y^(13+J*k)*τ))) :=by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hraw (hp u)) (coef u)) (abs_nonneg _)
    _ = (|c u| *(t u*b u))*(WilsonEmittedTransitionJet.fee J (shift u) 1*
      fixed G J d (pieces u))*y^(13+J*k)*τ:=by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hτ
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans hh) _)
      apply mul_le_mul_of_nonneg_left paid
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (hp u) (old u).1)

end YM.Integration.WilsonEmittedJoinedFares
end
