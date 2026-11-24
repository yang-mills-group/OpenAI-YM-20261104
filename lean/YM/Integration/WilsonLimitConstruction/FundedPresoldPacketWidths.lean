import YM.Integration.WilsonLimitConstruction.FundedNativePacketGeometry
import YM.Integration.ActualRunComponentAdmission
import YM.WilsonCoeffUV.Root.UV.InstallRoot
import YM.FullVolume.Cross
import YM.Push.PRICE_COMPILER.Basic

/-! The actual finite marked pulse is already a function of the original
sheet kernel and two adjacent discrete stages. Its funding therefore does
not require the realized inverse coupling, volume or chosen packet model. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPresoldPacketWidths
open Filter Lattice Wilson RG RG.Supply Precision Marker FullQLocal FullQLocal.RenderedStep
open PhysicalNext.Repeat.Legato Push.PriceCompiler
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Mer.Rolls
open scoped Topology Classical

def branch (G : Gauge) (K : KernelChoices) (e k b i j : ℕ) : ℝ :=
  if h : (4 : ℕ) ≤ i ∧ (5 : ℕ) ≤ j then
    pulseV G (e+1) k b (min 1 (splash G K i j h.1 h.2))
      (lt_min zero_lt_one (spatter G K i j h.1 h.2).1)
  else (1 : ℝ)

theorem positive (G : Gauge) (K : KernelChoices) (e k b i j : ℕ) :
    0<branch G K e k b i j := by
  unfold branch
  split_ifs with h
  · exact ((rootBill G b k (e+1) (lt_min zero_lt_one (spatter G K i j h.1 h.2).1)).choose_spec.choose_spec).affordable
  · exact (zero_lt_one : (0:ℝ) < 1)

def profile (G : Gauge) (K : KernelChoices) (e k b : ℕ) (old : ProfileWidths) : ProfileWidths where
  width i := min (old.width i) (min (branch G K e k b i i) (branch G K e k b i (i+1)))
  positive i := lt_min (old.positive i)
    (lt_min (positive G K e k b i i) (positive G K e k b i (i+1)))

theorem earlier (G : Gauge) (K : KernelChoices) (e k b : ℕ) (old : ProfileWidths) (i : ℕ) :
    (profile G K e k b old).width i ≤ old.width i := min_le_left _ _

theorem adjacent (G : Gauge) (K : KernelChoices) (e k b : ℕ) (old : ProfileWidths) {i j : ℕ}
    (step : StepStages j i) : (profile G K e k b old).width i ≤ branch G K e k b i j := by
  rcases step with ⟨lo,hi⟩
  rcases (show j=i ∨ j=i+1 by omega) with rfl|rfl
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

variable {G : Gauge} (R : Run G) {e : ℕ} (k b : ℕ) (old : ProfileWidths)
local notation "L₀" => R.family.path.levels
local notation "W₀" => profile G (L₀).clock.kernel e k b old

theorem live (m : ℕ) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (five : 5 ≤ (L₀).clock.J (m+1)) (stamp : (Q.mint m hm).σ=crestM (L₀) m five) :
    (W₀).width ((L₀).clock.J m) ≤ VestS b k Q m hm := by
  let i := (L₀).clock.J m
  let j := (L₀).clock.J (m+1)
  have hi : 4 ≤ i := (L₀).clock.adm m
  have sold := adjacent G (L₀).clock.kernel e k b old (step_paid (L₀) m)
  have read : branch G (L₀).clock.kernel e k b i j=VestS b k Q m hm := by
    simp only [branch,dif_pos (And.intro hi five),VestS,Vσ,stamp,crestM,i,j]
  exact sold.trans read.le

theorem pulse (m : ℕ) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (five : 5 ≤ (L₀).clock.J (m+1)) (stamp : (Q.mint m hm).σ=crestM (L₀) m five) :
    (W₀).pair R.family m/2 ≤ VestS b k Q m hm := by
  have bound : (W₀).pair R.family m ≤ (W₀).width ((L₀).clock.J m) := min_le_right _ _
  calc
    (W₀).pair R.family m/2 ≤ (W₀).pair R.family m := by linarith only [(W₀).pair_positive R.family m]
    _ ≤ _ := bound.trans (live R k b old m Q hm five stamp)

variable {V : Type} [DecidableEq V] [Fintype V] (J : Request V)

omit [DecidableEq V] [Fintype V] in
theorem geometry (hG : G.Simple) (W : ProfileWidths) (p : WidthPayment R.family W) :
    ∀ᶠ m : ℕ in atTop, ∀ A : NumericSchedule R.family J,
      (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ) ≤ (W.pair R.family m/2)/4 := by
  let f : ℕ→ℝ := fun m=>Real.log ((L₀).clock.hatBeta m)
  have big : Tendsto f atTop atTop := Real.tendsto_log_atTop.comp (WardBin.bell (L₀) hG)
  have D : 0<4*J.outputSupport := mul_pos (by norm_num) J.output_support_pos
  filter_upwards [ActualRunComponentAdmission.rate_scale R.family W p hG _ D,big.eventually_ge_atTop 1]
    with m paid hi
  intro A
  let rate := ActualRunComponentAdmission.rate R.family W m
  have rpos : 0<rate := ActualRunComponentAdmission.rate_pos R.family W m
  have ceil : (f m)^2 ≤ ((A.outputNorm m).B:ℝ) := by
    rw [(A.output_norm m).block]
    exact Nat.le_ceil _
  have covers : (A.outputNorm m).supportExponent*rate⁻¹ ≤ ((A.outputNorm m).B:ℝ)/4 := by
    rw [(A.output_norm m).reserve]
    change 4*J.outputSupport*rate⁻¹ ≤ f m at paid
    have quad := mul_le_mul_of_nonneg_right hi (zero_le_one.trans hi)
    nlinarith only [paid,ceil,quad]
  exact (FundedNativePacketGeometry.reserve (A.outputNorm m) rpos covers le_rfl).trans
    (div_le_div_of_nonneg_right (ActualRunComponentAdmission.rate_width R.family W m) (by norm_num))

end YM.Integration.WilsonLimitConstruction.FundedPresoldPacketWidths
end
