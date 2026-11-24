import YM.Integration.WilsonPositionRawPolynomial
import YM.Integration.WilsonPositionRawCutoff
import YM.Integration.WilsonPositionRawDetector

/-! The finite raw Wilson panel read in its calibrated auxiliary variable.
The numerical coordinate is set by the three graded cutoff fields on the
original physical hierarchy before either limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionMeasuredRawPanel
open Filter Function Finset Set Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb RG17 Trace.Pilot PhysMS PhysicalNext.Repeat.Legato
open WilsonPositionRawMesh WilsonPositionRawFiling WilsonPositionRawDetector WilsonPositionRawCutoff
open WilsonPositionSeparatedProfileMatching
open scoped BigOperators Topology Classical
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG T σ dial)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n) (q : ℕ)
    {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S) (J : ℝ → tower S)
    {l : Ultrafilter (ℕ × ℕ)} {Y : (Bel R.family.book).Hierarchy}
    (A : ℝ → WilsonPositionThermometerCapStation.Group R.family 6)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "τ" => thermometer Z F J A
local notation "seen" => observed Z F J none d φ v

def panel (i : ℕ) (r : ℝ) (z : ℕ × ℕ) : ℂ :=
  (PowerSeries.trunc (q+1) (said (published Z (Z.run.step i) d) φ v)).eval
    (bare Z (Z.run.step i) q (τ r z) : ℂ)

include H in
theorem booked (hq : 1 ≤ q) (lead : Leading F J)
    (book : WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J) (prior : (l : Filter _) ≤ f.fuse)
    (coupled : Coupling G θ) (source : ℝ → (ℕ × ℕ) → ℂ)
    (live : ∀ᶠ r in trail, Tendsto (source r) (l : Filter _) (𝓝 (seen r)))
    (paid : ∀ δ > 0, ∀ᶠ r in trail, ∃ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (θ r),
      (1+mass Z (Z.run.step i) q)^q*|θ r| ≤ δ ∧
      ∀ᶠ z : ℕ × ℕ in (l : Filter _),
        ‖source r z-panel Z d φ v q F J A i r z‖ ≤ δ*|θ r|^q) :
    WilsonPositionAuxiliaryMatch.booked Z F J d φ v q := by
  let axis := fun i r z=>bare Z (Z.run.step i) q (τ r z)
  apply on_axis Z H d φ v q F J axis lead A book prior coupled source live
  intro δ hd
  let c : ℝ := 8^(q+1)
  have c1 : 1 ≤ c := one_le_pow₀ (by norm_num)
  let e := min (1/32:ℝ) (δ/c)
  have ep : 0 < e := lt_min (by norm_num) (div_pos hd (by linarith))
  have width : e ≤ 1/32 := min_le_left .. 
  have expandFee : c*e ≤ δ := by
    rw [mul_comm,← le_div_iff₀ (by linarith : 0 < c)]
    exact min_le_right ..
  have fee : e ≤ δ := le_trans (le_mul_of_one_le_left ep.le c1) expandFee
  have registered := (goesFront (Expense.Stretched.runs Z.run)).eventually (Rose.usable Z.scheme Z.criterion hG)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((ready Z hG).and registered)
  have cold := coupled.conforms hG
  have late := (WilsonPositionAuxiliaryMesh.grows Z.run q trail coupled.positive cold).eventually_ge_atTop N
  have tiny : ∀ᶠ r in trail, |θ r| ≤ 1/8 := (cold.abs.eventually_lt_const (by norm_num)).mono fun _ h=>h.le
  filter_upwards [late,tiny,paid e ep,measured Z F J lead A book hG prior,coupled.positive] with r hh ht put reports warm
  obtain ⟨i,hi,bill,issued⟩ := put
  obtain ⟨first,usable⟩ := hN i (hh.trans hi)
  refine ⟨i,hi,?_⟩
  have heard := Metric.tendsto_nhds.mp reports _ (abs_pos.mpr warm.ne')
  filter_upwards [heard,issued] with z near test
  let b := mass Z (Z.run.step i) q
  have bp : 0 ≤ b := sum_nonneg fun _ _=>abs_nonneg _
  have bpay : b ≤ (1+b)^q :=
    calc b ≤ 1+b := by linarith
         _ = (1+b)^1 := (pow_one _).symm
         _ ≤ _ := pow_le_pow_right₀ (by linarith) hq
  have bound : |τ r z| ≤ 2*|θ r| := by
    rw [Real.dist_eq] at near
    have step := abs_sub_abs_le_abs_sub (τ r z) (θ r)
    linarith [le_abs_self (|τ r z|-|θ r|)]
  have small : 4*|τ r z| ≤ 1 := by linarith
  have amount : b*|θ r| ≤ e := (mul_le_mul_of_nonneg_right bpay (abs_nonneg _)).trans bill
  have cost : 16*b*|τ r z| ≤ 1 := by
    nlinarith only [mul_le_mul_of_nonneg_left bound bp,amount,width]
  have actual := WilsonPositionRawDetector.set Z _ q hq first _ small cost
  have axisBound : |axis i r z| ≤ 8*|θ r| := by dsimp [axis];linarith [actual.1]
  have same : forward Z (Z.run.step i) q (axis i r z) = τ r z := actual.2
  refine ⟨axisBound.trans (by linarith),same ▸ bound.trans (by linarith),?_,?_,?_⟩
  · rw [WilsonPositionRawPolynomial.issued Z _ q d φ v usable]
    exact test.trans (mul_le_mul_of_nonneg_right fee (pow_nonneg (abs_nonneg _) _))
  · rw [same,sub_self,abs_zero]
    positivity
  · calc
      _ ≤ (1+b)^q*(8*|θ r|)^(q+1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) axisBound _) (by positivity)
      _ = c*((1+b)^q*|θ r|)*|θ r|^q := by rw [mul_pow,pow_succ |θ r|];dsimp [c];ring
      _ ≤ δ*|θ r|^q := mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left bill (by linarith)).trans expandFee) (pow_nonneg (abs_nonneg _) _)

end YM.Integration.WilsonPositionMeasuredRawPanel
