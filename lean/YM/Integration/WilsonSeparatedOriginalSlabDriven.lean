import YM.Integration.WilsonSeparatedOriginalSlabFourierDeposit
import YM.RG05Readout.Capture.Line

/-! The actual joint centre of a Fourier packet on the registered compact cell is an affordable unary test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabDriven
open Function Finset Set MeasureTheory RG Lattice Wilson Source RG05Readout RG05Readout.Native
open WilsonSeparatedOriginalSlabCenterPhase WilsonSeparatedOriginalSlabCenterBill
open private chartTest from YM.Integration.WilsonSeparatedOriginalSlabFourierDeposit
open scoped BigOperators Classical Topology
variable {I:Type}[Fintype I]

def nativeChart : Body→ₗ[ℂ]C(Axis→ℝ,ℂ) where
  toFun:=chartTest
  map_add' _ _:=by ext; rfl
  map_smul' _ _:=by ext; rfl

def raw (v:I→Axis→ℝ):PulseC:=(invoice v).comp nativeChart

def tariff : ℝ:=1+volume.real Native.box

theorem positive : 0<tariff:=by unfold tariff; positivity

def filed (v:I→Axis→ℝ):PulseC:=(tariff:ℂ)⁻¹ • raw v

theorem extent (v:I→Axis→ℝ)(d:ℕ):Priced d (raw v) tariff:=by
  intro f c hc
  change ‖∫z in Native.box,f.val z * center v z‖≤_
  have h : ‖∫z in Native.box,f.val z*center v z‖≤c*volume.real Native.box:=by
    apply norm_setIntegral_le_of_norm_le_const Pert.Cellular.cells_compact.measure_lt_top
    intro z hz
    rw [norm_mul,show ‖center v z‖=1 from unit _ _,mul_one]
    simpa only [norm_iteratedFDeriv_zero] using hc 0 (Nat.zero_le _) z hz
  rw [mul_comm] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hc.nonneg)

theorem priced (v:I→Axis→ℝ)(d:ℕ):Priced d (filed v) 1:=by
  intro f c hc
  rw [one_mul]
  change ‖(tariff:ℂ)⁻¹*raw v f‖≤c
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg positive.le]
  exact (inv_mul_le_iff₀ positive).mpr (extent v d f c hc)

theorem restored (v:I→Axis→ℝ)(f:Body):
    (tariff:ℂ)*filed v f=invoice v (chartTest f):=by
  change (tariff:ℂ)*((tariff:ℂ)⁻¹*raw v f)=raw v f
  rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast positive.ne'),one_mul]

end YM.Integration.WilsonSeparatedOriginalSlabDriven
