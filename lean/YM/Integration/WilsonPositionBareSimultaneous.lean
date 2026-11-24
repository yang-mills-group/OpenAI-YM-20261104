import YM.Integration.WilsonOriginalPositionFineScheme

/-! Tune one real auxiliary bare scalar to a reported position thermometer. The
degree of the scalar polynomial is chosen before either physical regulator, and
grows slowly enough that every fixed truncation on this same scalar is valid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionBareSimultaneous
open Filter Finset Function Lattice Wilson RG Extraction Spec Maxwell
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb XSpace FVA2 FVA2.Register
open FVA2.Scale MS MS.Land MS.Fleet
open WilsonPositionRawMesh WilsonPositionRawDetector
open scoped Topology BigOperators Classical
variable {G:Gauge} (Z:WilsonPrescription G)

theorem omitted (m:Mesh) (n q:ℕ) (order:q≤n) (x:ℝ) (small:|x|≤1) :
    |forward Z m n x-forward Z m q x| ≤ mass Z m n*|x|^(q+1) := by
  let c (k:ℕ) := (PowerSeries.coeff k (Rose.chosen Z.scheme Z.criterion m)).re
  let a (k:ℕ) := c k*x^k
  have evaluated (j:ℕ) : forward Z m j x=∑ k ∈ range (j+1),a k := Fin.sum_univ_eq_sum_range a (j+1)
  have rent : mass Z m n = ∑ k∈range (n+1),|c k| := Fin.sum_univ_eq_sum_range (fun k=>|c k|) (n+1)
  have cut := sum_range_add_sum_Ico a (Nat.add_le_add_right order 1)
  rw [evaluated,evaluated,show (∑ k ∈ range (n+1),a k)-(∑ k∈range (q+1),a k) =
      ∑ k∈Ico (q+1) (n+1),a k by linarith,rent,sum_mul]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (g:=fun k=>|c k| *|x|^(q+1)) ?_).trans
  · exact sum_le_sum_of_subset_of_nonneg (fun k hk=>mem_range.mpr (mem_Ico.mp hk).2)
      (fun k _ _=>mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
  · intro k hk
    change |c k*x^k| ≤ |c k| * |x|^(q+1)
    rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg _) small (mem_Ico.mp hk).1) (abs_nonneg _)

variable (index:ℝ→ℕ) (t:ℝ→ℝ)
private def admissible (r:ℝ) (s:ℕ) : Prop :=
  64*(s+2:ℝ)*(1+mass Z (Z.run.step (index r)) (s+1))*t r ≤ 1

def degree (r:ℝ) : ℕ := Nat.findGreatest (admissible Z index t r) (index r)+1

def parameter (r value : ℝ) : ℝ := bare Z (Z.run.step (index r)) (degree Z index t r) value

variable {R : Run G} (hG:G.Simple) {B:ℕ} (hB:0<B) (pace:WilsonWindowReportingPace.Slow R.kit)
    (physical:Coupling G t) {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial)
    {fine:ℝ→ℕ} (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=hG) (B:=B) Z fine index)

include hB pace H physical schedule in
private theorem controls :
    (∀ s:ℕ,∀ᶠ r in trail,admissible Z index t r s) ∧ Tendsto index trail atTop := by
  have floors := WilsonPositionProgramInversionBill.interval R hG hB pace t physical Z H 1 (show 0<(1:ℝ) by norm_num)
  have grows := WilsonPositionAuxiliaryMesh.grows Z.run 1 trail physical.positive (physical.conforms hG)
  refine ⟨?_,tendsto_atTop.mpr fun k=>?_⟩
  · intro s
    have fee := WilsonPositionProgramInversionBill.interval R hG hB pace t physical Z H (s+1)
      (show 0<(1:ℝ)/(64*(s+2:ℝ)) by positivity)
    filter_upwards [schedule,physical.positive,fee] with r hm hot pay
    let v := mass Z (Z.run.step (index r)) (s+1)
    have hv : 0≤v := sum_nonneg fun _ _=>abs_nonneg _
    have cash := (pay (index r) hm.2.1 hm.2.2.1).2.2
    change (1+v)^(s+1)*|t r| ≤ _ at cash
    rw [abs_of_pos hot] at cash
    have small := (mul_le_mul_of_nonneg_right (le_self_pow₀ (by linarith : 1≤1+v)
      (Nat.succ_ne_zero s)) hot.le).trans cash
    have h := (le_div_iff₀ (show 0<64*(s+2:ℝ) by positivity)).mp small
    change 64*(s+2:ℝ)*(1+v)*t r ≤ 1
    linarith
  · filter_upwards [schedule,floors,grows.eventually_ge_atTop k] with r hm found late
    exact late.trans (found (index r) hm.2.1 hm.2.2.1).1

include hB pace H physical schedule in
theorem calendar :
    Tendsto (degree Z index t) trail atTop ∧
    ∀ᶠ r in trail, 64*(degree Z index t r+1:ℝ)*(1+mass Z (Z.run.step (index r)) (degree Z index t r))*t r ≤ 1 := by
  obtain ⟨bids,goes⟩ := controls Z index t hG hB pace physical H schedule
  refine ⟨tendsto_atTop.mpr (fun s=>?_),?_⟩
  · filter_upwards [bids s,goes.eventually_ge_atTop s] with r quote n
    exact (Nat.le_findGreatest n quote).trans (Nat.le_succ _)
  · filter_upwards [bids 0] with r quote
    have h := Nat.findGreatest_spec (Nat.zero_le (index r)) quote
    simpa only [admissible,degree,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using h

include hB pace H physical schedule in
theorem priced (q:ℕ) (δ:ℝ) (positive:0<δ) :
    ∀ᶠ r in trail,∀ value:ℝ, |value| ≤ 2*t r →
      |parameter Z index t r value| ≤ 8*t r ∧
      forward Z (Z.run.step (index r)) (degree Z index t r) (parameter Z index t r value)=value ∧
      |forward Z (Z.run.step (index r)) q (parameter Z index t r value)-value| ≤ δ*|t r|^q := by
  obtain ⟨orders,paid⟩ := calendar Z index t hG hB pace physical H schedule
  have iLate := (controls Z index t hG hB pace physical H schedule).2
  have ready:=iLate.eventually (WilsonPositionRawDetector.ready Z hG)
  obtain ⟨k,hk⟩ := exists_nat_gt ((8:ℝ)^(q+1)/δ)
  have μ:= (physical.conforms hG).eventually_lt_const (show 0<(1:ℝ)/8 by norm_num)
  filter_upwards [paid,ready,physical.positive,μ,orders.eventually_ge_atTop k,orders.eventually_ge_atTop q]
    with r money first hot small order targetQ
  let d:=degree Z index t r
  let v:=mass Z (Z.run.step (index r)) d
  have hv : 0≤v := sum_nonneg fun _ _=>abs_nonneg _
  have hd : 0≤(d:ℝ):=by positivity
  change 64*(d+1:ℝ)*(1+v)*t r≤1 at money
  have one : v*t r*(d+1:ℝ) ≤ 1 := by
    have ve := mul_nonneg hv hot.le
    have de := mul_nonneg hd hot.le
    have vd := mul_nonneg hd ve
    nlinarith only [money,ve,de,vd,hot]
  intro value bound
  have hfit := WilsonPositionRawDetector.set Z (Z.run.step (index r)) d (by dsimp [d,degree];omega)
    first value (by linarith) (by
      have wait := mul_le_mul_of_nonneg_left bound hv
      nlinarith only [money,wait,mul_nonneg hv hot.le,mul_nonneg hd hot.le,mul_nonneg hd (mul_nonneg hv hot.le),hot])
  let u:=parameter Z index t r value
  change |u|≤4*|value| ∧ forward Z (Z.run.step (index r)) d u=value at hfit
  have wallet : |u|≤8*t r:=by linarith only [hfit.1,bound]
  refine ⟨wallet,hfit.2,?_⟩
  change |forward Z (Z.run.step (index r)) q u-value| ≤ δ*|t r|^q
  rw [←hfit.2,abs_sub_comm,abs_of_pos hot]
  have hcut:=omitted Z (Z.run.step (index r)) d q targetQ u (wallet.trans (by linarith))
  have kbig : (k:ℝ)≤d:=by exact_mod_cast order
  have major : (8:ℝ)^(q+1) ≤ δ*(d+1:ℝ) := by
    have debt:=(div_lt_iff₀ positive).mp hk
    nlinarith only [debt,mul_le_mul_of_nonneg_right kbig positive.le,positive]
  have price : v*t r*8^(q+1) ≤ δ := by
    calc v*t r*8^(q+1) ≤ v*t r*(δ*(d+1:ℝ)) :=
           mul_le_mul_of_nonneg_left major (mul_nonneg hv hot.le)
         _ = δ*(v*t r*(d+1:ℝ)) := by ring
         _ ≤ δ := mul_le_of_le_one_right positive.le one
  apply hcut.trans
  calc v*|u|^(q+1) ≤ v*(8*t r)^(q+1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) wallet _) hv
       _ = (v*t r*8^(q+1))*(t r)^q := by rw [mul_pow,pow_succ (t r)];ring
       _ ≤ δ*(t r)^q := mul_le_mul_of_nonneg_right price (pow_nonneg hot.le _)

end YM.Integration.WilsonPositionBareSimultaneous
