import YM.Integration.WilsonPhysicalStationPrincipalGrade

/-! Engineering, magnetization, and thermal factors of the actual two raw
coordinates. All compensation is evaluated at the endpoints of one window. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalStationEndCurrency
open RG Labels Source Lattice Wilson Extra.Histories Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph Work.G08 Next.Foundations
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) (d N p m k : ℕ)
local notation "C" => R.family
local notation "A" => R.family.path.levels
def row (w q : ℕ) (r : ℝ) : ℝ :=
  (R.family.S.a m)^d * (shrink R.family m N p)⁻¹^q * r^w
def charge (w q z : ℕ) (r s : ℝ) : ℝ :=
  row R d N p k w q s / row R d N p m w z r

private theorem grades (a b u v r s : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0)
    (hv : v ≠ 0) (hr : r ≠ 0) (w q j n : ℕ) :
    (b^(w+n) * v⁻¹^q * s^w) / (a^(w+n) * u⁻¹^(q+j) * r^w) =
    (b/a)^n * ((b*s)/(a*r))^w * (u/v)^q * u^j := by
  simp only [pow_add, mul_pow, div_pow, inv_pow]; field_simp

theorem projected (w q z : ℕ) (r s : ℝ) (hr : 0 < r) (hm : m ≤ N)
    (hk : k ≤ N) (hd : w ≤ d) (hq : q ≤ z) :
    charge R d N p m k w q z r s =
      (R.family.S.a k / R.family.S.a m)^(d-w) *
      ((R.family.S.a k * s) / (R.family.S.a m * r))^w *
      (shrink R.family m N p / shrink R.family k N p)^q *
      (shrink R.family m N p)^(z-q) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hd
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hq
  simpa only [charge,row,Nat.add_sub_cancel_left] using
    grades (R.family.S.a m) (R.family.S.a k) (shrink R.family m N p) (shrink R.family k N p)
      r s (R.family.S.a_pos m).ne' (R.family.S.a_pos k).ne'
      (shrink_pos R.family R.makes hm p).ne' (shrink_pos R.family R.makes hk p).ne' hr.ne' w q j n

theorem primary (w q : ℕ) (r s : ℝ) (hr : 0 < r) (hm : m ≤ N) (hk : k ≤ N) (hd : w ≤ d) :
    charge R d N p m k w q q r s *
      (((A).budget m).threshold / ((A).budget k).threshold)^q *
      (R.family.S.a m / R.family.S.a k)^(d-w) =
      ((R.family.S.a k * s) / (R.family.S.a m * r))^w *
      (((Real.sqrt (R.family.path.β N p m))⁻¹) / ((Real.sqrt (R.family.path.β N p k))⁻¹))^q := by
  have balance : shrink R.family m N p / shrink R.family k N p *
      (((A).budget m).threshold / ((A).budget k).threshold) =
      ((Real.sqrt (R.family.path.β N p m))⁻¹) / ((Real.sqrt (R.family.path.β N p k))⁻¹) := by
    unfold shrink
    change ((_ / ((A).budget m).threshold) / (_ / ((A).budget k).threshold)) * _ = _
    rw [div_div_eq_mul_div,div_mul_div_comm]
    field_simp [((A).budget m).threshold_pos.ne',((A).budget k).threshold_pos.ne']
  have gap : R.family.S.a k / R.family.S.a m * (R.family.S.a m / R.family.S.a k) = 1 := by
    field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos k).ne']
  rw [projected R d N p m k w q q r s hr hm hk hd le_rfl, Nat.sub_self,pow_zero,mul_one]
  calc
    _ = (R.family.S.a k / R.family.S.a m * (R.family.S.a m / R.family.S.a k))^(d-w) *
        ((R.family.S.a k * s) / (R.family.S.a m * r))^w *
        (shrink R.family m N p / shrink R.family k N p *
          (((A).budget m).threshold / ((A).budget k).threshold))^q := by rw [mul_pow,mul_pow]; ring
    _ = _ := by rw [gap,one_pow,one_mul,balance]

end YM.Integration.WilsonPhysicalStationEndCurrency
