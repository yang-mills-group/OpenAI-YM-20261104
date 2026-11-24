import YM.Integration.WilsonOriginalSignedHighModes
import YM.Integration.WilsonOriginalTemperatureDecay

/-! The infinite part of the derivative series at the actual physical
temperature, including the published finite-order subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedTailSum
open Filter Function Finset Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalIntegerModeCut (size)
open WilsonOriginalLowFourierJets (cube jet)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalTestedFourierBank (Prices)

def high {d j : ℕ} (u : ℝ) (axis : Fin j → Fin d) (unit : Fin j → ℂ)
    (phase residual : (Fin d → ℤ) → ℂ) (v : Fin d → ℤ) : ℂ :=
  if v ∈ cube d ⌊(u⁻¹)^12⌋₊ then 0 else phase v*jet axis unit v*residual v

def remainder {d : ℕ} (u : ℝ) (Q : ℕ) (read : (Fin d → ℤ) → ℂ)
    (coeff : ℕ → (Fin d → ℤ) → ℂ) (v : Fin d → ℤ) : ℂ :=
  read v - ∑ e : Fin (Q+1), (u:ℂ)^e.val*coeff e.val v

theorem original {G : Gauge} {d j : ℕ} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (Q p : ℕ) (axis : Fin j → Fin d) (unit : Fin j → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in trail, ∀ phase : (Fin d → ℤ) → ℂ,
      (∀ v, ‖phase v‖ ≤ 1) → let u := warm r
      let tail := high u axis unit phase (remainder u Q (read r) coeff)
      Summable (fun v => ‖tail v‖) ∧ ∑' v, ‖tail v‖ ≤ C*ε*u^p := by
  obtain ⟨L,hL,addModes⟩ := WilsonOriginalFourierLattice.original d
  let M := ∏ i, ‖unit i‖
  have hM : 0 ≤ M := prod_nonneg fun _ _ => norm_nonneg _
  refine ⟨L*M*2^(2*d)*((Q:ℝ)+2),by positivity,?_⟩
  intro ε he
  obtain ⟨S,hS,field⟩ := WilsonOriginalSignedHighModes.original hG paid b Q j p he
  have hpos : 0 < S := zero_lt_one.trans_le hS
  have cold := WilsonOriginalTemperatureDecay.original paid
  have below := (tendsto_order.mp cold).2 S⁻¹ (inv_pos.mpr hpos)
  filter_upwards [paid.positive,below,field,(tendsto_order.mp cold).2 1 zero_lt_one]
      with r hu small income hu1 phase unitPhase
  let u := warm r
  let rawCash := (2:ℝ)^(2*d)*((Q:ℝ)+2)*ε*u^p
  have cash : 0 ≤ rawCash := by dsimp [rawCash,u];positivity
  have gate : S ≤ u⁻¹ := by
    rw [← one_div,le_div_iff₀ hu,mul_comm]
    apply (le_div_iff₀ hpos).mp
    simpa [one_div] using small.le
  let tail := high u axis unit phase (remainder u Q (read r) coeff)
  have per (v) : ‖tail v‖ ≤ M*rawCash*(1+(height v:ℝ))⁻¹^(2*d) := by
    by_cases hv : v ∈ cube d ⌊(u⁻¹)^12⌋₊
    · simp only [tail,high,if_pos hv,norm_zero];positivity
    obtain ⟨above,enters⟩ := WilsonOriginalIntegerModeCut.outside hu hv
    have one := income v (gate.trans above.le) hu hu1.le enters
    let den := (1+(height v:ℝ))^(2*d)
    have denpos : 0 < den := by dsimp [den];positivity
    have rate : (size v^12)^j*‖remainder u Q (read r) coeff v‖ ≤ rawCash/den :=
      (le_div_iff₀ denpos).mpr (by simpa only [den,remainder,rawCash,u,WilsonOriginalIntegerModeCut.size_pow] using one)
    have term := WilsonOriginalIntegerModeCut.original axis unit v
    simp only [tail,high,if_neg hv,norm_mul]
    calc
      _ ≤ (1*(M*(size v^12)^j))*‖remainder u Q (read r) coeff v‖ := by gcongr;exact unitPhase v
      _ = M*((size v^12)^j*‖remainder u Q (read r) coeff v‖) := by ring
      _ ≤ M*(rawCash/den) := mul_le_mul_of_nonneg_left rate hM
      _ = _ := by simp [den,div_eq_mul_inv,mul_assoc]
  obtain ⟨conv,total⟩ := addModes (M*rawCash) (mul_nonneg hM cash) tail per
  refine ⟨conv,total.trans_eq ?_⟩
  dsimp only [rawCash];ring

end YM.Integration.WilsonOriginalSignedTailSum

