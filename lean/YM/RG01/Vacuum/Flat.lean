import YM.Next.WARD_BIN.Hats

/-! # Arithmetic for coupling-flat shares

Take constants depending on the common construction/enlargement but not
N, scale, torus size or tag census. `currency` consumes actual β on the
fine (or coarse) side of a step, no matching to an external scheme.
Includes arbitrary *fixed* extra powers of hatBeta (needed when
recovering marked/resolvent or inverse-scalar costs), not `Calendar.J`
orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum.Flat
open Function Set Filter Lattice Wilson RG Real WardBin
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (T : Levels G) (hG : G.Simple)

include hG
lemma nextComparable : ∀ᶠ i in atTop, T.clock.hatBeta (i+1) ≤ 2*T.clock.hatBeta i := by
  filter_upwards [T.fits.mesh.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    T.S.divergent.eventually_gt_atTop 0] with i hi he
  have hS : Real.log (T.S.block i).val ≤ T.S.scale i := by
    have hh : Real.log (T.S.block i).val / T.S.scale i ≤ 1 := hi
    simpa using (div_le_iff₀ he).mp hh
  have hg := Gauge.slopeConstant_pos hG
  unfold Calendar.hatBeta
  rw [Schedule.scale_succ]
  nlinarith only [T.clock.bar_pos, mul_le_mul_of_nonneg_left hS hg.le]

/-- One lower-bound-independent constant covers even all adjacent
steps (convert the prefix explicitly, using the committed calendar only). -/
lemma adjacentBound : ∃ D : ℝ, 1 ≤ D ∧ ∀ i, T.clock.hatBeta (i+1) ≤ D*T.clock.hatBeta i := by
  obtain ⟨i,hi⟩:= eventually_atTop.mp (nextComparable T hG)
  let H (m : ℕ):= T.clock.hatBeta m
  let S := Finset.range i
  let f (j : ℕ) := H (j+1)
  let D := 2+S.sum f
  have h : 0 ≤ S.sum f := Finset.sum_nonneg fun _ _=> (WardBin.hot T _).le
  refine ⟨D,by unfold D; linarith,fun m=> ?_⟩
  rcases lt_or_ge m i with ht|ht
  · have hh : H (m+1) ≤ S.sum f:=Finset.single_le_sum (f:=f) (fun _ _=> (WardBin.hot T _).le) (Finset.mem_range.mpr ht)
    apply hh.trans
    apply le_trans (le_add_of_nonneg_left (show (0:ℝ)≤2 by norm_num))
    exact le_mul_of_one_le_right (by linarith) (T.fits.delayed _).le
  exact (hi m ht).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right h) (WardBin.hot T _).le)

/-- Detector currency at weight d. Finiteness and smallness established
from the accepted same-calendar exponential monitor asymptotics. -/
def price (d m : ℕ) : ℝ:= (T.clock.hatCoupling m)⁻¹ ^ d * sqrt (T.clock.forcedAllowance m)
def frontToll (d m : ℕ) : ℝ:= 1+(Finset.range m).sum (price T d)
lemma monitorAudit (d : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ i, price T d i ≤ c := by
  let f:= price T d
  obtain ⟨i,hi⟩:= eventually_atTop.mp ((WardBin.pale T hG d).eventually (ge_mem_nhds zero_lt_one))
  have hf (i : ℕ):0≤ f i:=by unfold f price Calendar.forcedAllowance Calendar.hatCoupling; positivity
  have hS : 0 ≤ (Finset.range i).sum f:=Finset.sum_nonneg fun i _=> hf i
  refine ⟨frontToll T d i, by unfold frontToll; change 0 ≤ 1+(Finset.range i).sum f; positivity, fun j=>?_⟩
  rcases lt_or_ge j i with hv|hu
  · exact (Finset.single_le_sum (fun k (_:k∈Finset.range i)=> hf k) (Finset.mem_range.mpr hv)).trans (le_add_of_nonneg_left zero_le_one)
  exact (hi j hu).trans (le_add_of_nonneg_right hS)

/-- Coupling-flat certificate suitable for the charged budgets. Covers any b
in either of the two physical bands at this step. Absorb k extra fine inverse
scales as well as a p-th power remainder. -/
theorem currency (p k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ℕ) (b : ℝ),
    0 < b → (b ≤ 2*T.clock.hatBeta (i+1) ∨ b ≤ 2*T.clock.hatBeta i) →
      T.clock.hatBeta (i+1)^k * sqrt (T.clock.forcedAllowance i) ≤ C * (sqrt b)⁻¹^p := by
  obtain ⟨D,hD,H⟩:=adjacentBound T hG
  obtain ⟨c,hc,h⟩:=monitorAudit T hG (2*k+p)
  let a := (2*D:ℝ)
  let C := (sqrt a)^p*D^k*c
  have hd : 0≤D:=zero_le_one.trans hD
  have ha : 0<a:=by unfold a; linarith
  refine ⟨C,by unfold C; positivity,?_⟩
  intro i b hb hr
  let y:=T.clock.hatBeta i
  let u:=sqrt y
  let w:=sqrt (T.clock.forcedAllowance i)
  have hy:(1:ℝ)< y:= T.fits.delayed i
  have hu :0<u:=sqrt_pos.mpr (zero_lt_one.trans hy)
  have hw : 0 ≤ w:= sqrt_nonneg _
  have hm : b ≤ a*y := by
    rcases hr with hr|hr
    · exact hr.trans ((mul_le_mul_of_nonneg_left (H i) (by norm_num : (0:ℝ)≤2)).trans_eq (Eq.symm (mul_assoc ..)))
    exact hr.trans (mul_le_mul_of_nonneg_right (by unfold a; linarith only [hD]) (zero_le_one.trans hy.le))
  have hq : sqrt b ≤ sqrt a*u := by rw [← sqrt_mul ha.le]; exact sqrt_le_sqrt hm
  rw [inv_pow,← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have he : u^(2*k+p)*w ≤ c := by have hx:= h i; unfold price Calendar.hatCoupling at hx; simpa using! hx
  calc
    _ ≤ (D*y)^k*w * ((sqrt a*u)^p) := by gcongr <;> first | exact (WardBin.hot T _).le | exact H i
    _ = ((sqrt a)^p * D^k) * (u^(2*k+p)*w) := by
      rw [mul_pow,mul_pow,pow_add,pow_mul, show u^2=y from sq_sqrt (zero_le_one.trans hy.le)]; ring
    _ ≤ _ := by unfold C; gcongr

end YM.RG01.Vacuum.Flat
