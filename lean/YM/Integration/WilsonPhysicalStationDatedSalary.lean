import YM.Integration.WilsonPhysicalStationFactoryGerm

/-! Bounds for the actual original weak transfer and its factory salary at all
dates of a reporter interval, in the original (unscaled) coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedVariables false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationDatedSalary
open Filter Function RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph WilsonPhysicalStationFactoryGerm
open Work.G08 Next.Foundations
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem bank (i:ℕ) :
    ((A).params (i+1)).columns  ≤  Bid.puffs ((C).S.block i) ∧
    R.w.K ((A).clock.J (i+1))  ≤  Bid.puffs ((C).S.block i)  :=  by
  let s:ℝ := ((A).params (i+1)).columns
  let j := (A).clock.J (i+1)
  let u := R.w.K (j+1)
  have hs:1 ≤ s := ((A).params _).columns_ge
  have hu:1 ≤ u := R.w.prices _
  have booked:100000*u^6*(1+s)^2 ≤ Bid.puffs ((C).S.block i) := R.b.clock.bank i
  have h6:1 ≤ u^6 := one_le_pow₀ hu
  have h1:u ≤ u^6 := by
    simpa using (pow_le_pow_right₀ hu (show 1 ≤ 6 by decide))
  have hs2:s ≤ (1+s)^2 := by nlinarith only [hs,sq_nonneg s]
  have hs1:1 ≤ (1+s)^2 := hs.trans hs2
  have ha:(1+s)^2 ≤ 100000*u^6*(1+s)^2 := 
    le_mul_of_one_le_left (by linarith only [hs1]) (by linarith only [h6])
  have hb:u^6 ≤ 100000*u^6*(1+s)^2 := 
    (le_mul_of_one_le_left (by linarith only [h6]) (by norm_num : (1:ℝ) ≤ 100000)).trans
      (le_mul_of_one_le_right (by positivity) hs1)
  exact ⟨hs2.trans (ha.trans booked),(R.w.growth (Nat.le_succ j)).trans (h1.trans (hb.trans booked))⟩

theorem columns (i:ℕ) : ((A).params (i+1)).columns  ≤  (((C).S.block i).val:ℝ)  :=  by
  apply (bank R i).1.trans
  unfold Bid.puffs
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (((C).S.block i).val:ℝ) by exact_mod_cast ((C).S.block i).property)
      (by norm_num : (1:ℝ)/8 ≤ 1))

variable (d N p : ℕ)
def datedMass (R : Run G) (d N p : ℕ) (y : R.family.label d) (i : ℕ) : ℝ :=
  (R.family.labels.level d).coeffSize
    (WilsonPhysicalStationFactoryGerm.incoming R d N p y i).x
def span (m k:ℕ):ℝ := (C).S.a m/(C).S.a k

theorem span_succ (m k:ℕ):span R m (k+1)=span R m k*(((C).S.block k).val:ℝ) := by
  unfold span; rw [(C).S.a_step]; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring

theorem rising (payer : R.family.label d) (m n : ℕ) (start:(C).ref d ≤ m)(top:m+n ≤ N):
    datedMass R d N p payer (m+n)  ≤  span R m (m+n) * datedMass R d N p payer m  :=  by
  induction n with
  | zero => simp [span, ((C).S.a_pos m).ne']
  | succ n ih =>
    let i := m+n
    have hr:(C).ref d ≤ i := start.trans (Nat.le_add_right ..)
    have hnext:i < N := by dsimp [i]; omega
    have h :=  (R.makes.calibrated d N p (start.trans ((Nat.le_add_right m _).trans top))).back i hr hnext
      (((C).factory d N p).terminal.symm payer)
    change datedMass R d N p payer (i+1)  ≤  ((A).params (i+1)).columns * datedMass R d N p payer i at h
    change datedMass R d N p payer (i+1)  ≤  span R m (i+1)*datedMass R d N p payer m
    rw [span_succ]; apply h.trans
    have h0:0 ≤ datedMass R d N p payer i := by apply size_nonneg
    calc
      _  ≤  (((C).S.block i).val:ℝ) * datedMass R d N p payer i  :=  mul_le_mul_of_nonneg_right (columns R i) h0
      _  ≤  (((C).S.block i).val:ℝ) * (span R m i*datedMass R d N p payer m)  := 
        mul_le_mul_of_nonneg_left (ih (by omega)) (Nat.cast_nonneg _)
      _ = _  :=  by ring

theorem falling (payer : R.family.label d) (m n : ℕ) (start:(C).ref d ≤ m)(top:m+n ≤ N):
    datedMass R d N p payer m  ≤  span R m (m+n)^(d+1) * datedMass R d N p payer (m+n)  :=  by
  induction n with
  | zero => simp [span, ((C).S.a_pos m).ne']
  | succ n ih =>
    let i := m+n
    have hr:(C).ref d ≤ i := start.trans (Nat.le_add_right ..)
    have hnext:i < N := by dsimp [i]; omega
    have h :=  (R.makes.calibrated d N p (start.trans ((Nat.le_add_right m _).trans top))).front i hr hnext
      (((C).factory d N p).terminal.symm payer)
    change datedMass R d N p payer i  ≤  ((A).params (i+1)).columns * (((C).S.block i).val:ℝ)^d * datedMass R d N p payer (i+1) at h
    change datedMass R d N p payer m  ≤  span R m (i+1)^(d+1)*datedMass R d N p payer (i+1)
    have hh:datedMass R d N p payer i  ≤  (((C).S.block i).val:ℝ)^(d+1)*datedMass R d N p payer (i+1) := by
      apply h.trans
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right (columns R i)
        (pow_nonneg (Nat.cast_nonneg _) _)).trans_eq (mul_comm ..)) (size_nonneg ..)
    rw [span_succ, mul_pow]
    calc
      _  ≤  span R m i^(d+1)*datedMass R d N p payer i := ih (by omega)
      _  ≤  span R m i^(d+1)*((((C).S.block i).val:ℝ)^(d+1)*datedMass R d N p payer (i+1)) := 
        mul_le_mul_of_nonneg_left hh (pow_nonneg (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) _)
      _ = _  :=  by ring

end YM.Integration.WilsonPhysicalStationDatedSalary
