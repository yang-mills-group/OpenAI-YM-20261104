import YM.Integration.WilsonPositionProgramTrialKinetic
import YM.Integration.WilsonPositionProgramTrialCollarMesh
import YM.Integration.WilsonAddressedCollarWindow

/-! The original kinetic unit at the physically paid finite planting date.
The older mesh and the independent period have no role in this scalar price. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCollarKinetic
open Filter Function Set RG Lattice Wilson Source Extraction Table Spec Climb Trace.Pilot PhysMS
open OPE PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FVA2.Register Pert.Asymptotics XSpace
open WilsonInvariantActionPosition (berth)
open scoped Topology Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) (m K : ℝ→ℕ)
local notation "a" => R.family.S.a
local notation "β" => R.family.path.β
local notation "hat" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "g" => regulatorRun R.family
local notation "unit" => WilsonMaxwellThermometerKineticLog.unit G
local notation "Visit" => ℝ×(ℕ×ℕ)

def Corridor (A:ℝ) : Prop :=
  ∀ᶠ r in trail,m r≤K r ∧ Real.log (a (m r)/a (K r))≤A*Λ (m r)

include simple

theorem reporter (l:Filter Visit) (down : Tendsto Prod.fst l trail)
    (late : Tendsto m trail atTop) (height : Tendsto (fun r=>R.family.S.scale (m r)/LogV r) trail (𝓝 1))
    (admitted : ∀ᶠ w:Visit in l,m w.1≤w.2.1) :
    Tendsto (fun w:Visit=>g w.2.1 w.2.2 (m w.1)/unit w.1) l (𝓝 1) := by
  let s:=R.family.S.scale
  let beta:=fun w:Visit=>β w.2.1 w.2.2 (m w.1)
  have dates:=late.comp down
  have measured : Tendsto (fun w:Visit=>beta w/s (m w.1)) l (𝓝 (2*b0 G)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [dates.eventually (zeroUp_bound R.family R.makes ep),admitted] with w hw atTop
    exact (show |beta w/s (m w.1)-2*b0 G|<ε from hw w.2.1 w.2.2 atTop)
  have gross : Tendsto (fun w:Visit=>beta w/LogV w.1) l (𝓝 (2*b0 G)) := by
    have combined:=measured.mul (height.comp down)
    rw [mul_one] at combined
    apply combined.congr'
    filter_upwards [(R.family.S.divergent.comp dates).eventually_gt_atTop 0] with w here
    change beta w/s (m w.1)*(s (m w.1)/LogV w.1)=beta w/LogV w.1
    field_simp [show s (m w.1)≠0 from here.ne']
  have pos : 0<2*b0 G := b0_normalizes (G:=G) ▸ G.slopeConstant_pos simple
  have root := (Real.continuous_sqrt.tendsto (2*b0 G)).comp gross
  have ratio := (tendsto_const_nhds (x:=Real.sqrt (2*b0 G))).div root (Real.sqrt_pos.mpr pos).ne'
  rw [div_self (Real.sqrt_pos.mpr pos).ne'] at ratio
  refine ratio.congr' ?_
  filter_upwards [down.eventually (to_log_zoom.eventually_gt_atTop 0),admitted] with w high sold
  have warm : 0<beta w := Overlay.beta_positive R.makes.wilson sold
  change Real.sqrt (2*b0 G)/Real.sqrt (beta w/LogV w.1)=(Real.sqrt (beta w))⁻¹/(Real.sqrt (2*b0 G*LogV w.1))⁻¹
  rw [Real.sqrt_div' _ high.le,Real.sqrt_mul pos.le,div_inv_eq_mul]
  field_simp [(Real.sqrt_pos.mpr high).ne',(Real.sqrt_pos.mpr warm).ne']

theorem flow (l:Filter Visit) (down:Tendsto Prod.fst l trail)
    (late:Tendsto m trail atTop) (height:Tendsto (fun r=>R.family.S.scale (m r)/LogV r) trail (𝓝 1))
    {A:ℝ} (charged:Corridor R m K A) (admitted:∀ᶠ w:Visit in l,K w.1≤w.2.1) :
    Tendsto (fun w:Visit=>g w.2.1 w.2.2 (K w.1)/unit w.1) l (𝓝 1) := by
  have ok : ∀ᶠ w:Visit in l,m w.1≤w.2.1 := by
    filter_upwards [down.eventually charged,admitted] with w h live using h.1.trans live
  have report := reporter R simple m l down late height ok
  let z := fun r:ℝ=>Real.log (hat (m r))
  have high:Tendsto z trail atTop := (WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).comp late
  have first:=((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp high)
  have zeroth:=((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp high).const_mul 2
  let c:=2*(G.slopeConstant+1)
  have cash:Tendsto (fun r=>c*(A*Λ (m r))/hat (m r)) trail (𝓝 0) := by
    have paid:=(zeroth.add first).const_mul (c*A)
    simp only [mul_zero,add_zero] at paid
    apply paid.congr'
    filter_upwards with r
    have hp:=zero_lt_one.trans (R.family.path.levels.fits.delayed (m r))
    change c*A*(2*((z r)^0*Real.exp (-z r))+(z r)^1*Real.exp (-z r))=_
    rw [pow_zero,one_mul,pow_one,Real.exp_neg,Real.exp_log (by exact hp : 0<hat (m r))]
    change c*A*(2*(hat (m r))⁻¹+z r*(hat (m r))⁻¹)=c*(A*(2+z r))/_
    ring
  have ratio:Tendsto (fun w:Visit=>g w.2.1 w.2.2 (K w.1)/g w.2.1 w.2.2 (m w.1)) l (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [down.eventually charged,admitted,down.eventually (cash.eventually_lt_const ep)] with w h live fee
    have actual:=WilsonMaxwellThermometerKineticCorridor.original R simple (m w.1) (K w.1) w.2.1 w.2.2 h.1 live
    rw [Real.log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne'] at h
    have cp:0≤c:=by dsimp [c];have pos:=G.slopeConstant_pos simple;positivity
    exact (actual.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h.2 cp)
      (zero_lt_one.trans (R.family.path.levels.fits.delayed _)).le)).trans_lt fee
  have out:=ratio.mul report
  rw [one_mul] at out
  refine out.congr' ?_
  filter_upwards [ok] with w h
  have gp : 0<g w.2.1 w.2.2 (m w.1) := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson h))
  field_simp [gp.ne']

theorem optical (slow:WilsonWindowReportingPace.Slow R.kit) (late:Tendsto m trail atTop) (t:ℕ) :
    Corridor R m (fun r=>berth R t (m r)) (t+1) := by
  filter_upwards [late.eventually (WilsonAddressedCollarWindow.original R simple slow t zero_lt_one)] with r paid
  refine ⟨paid.1.le,?_⟩
  have log := Real.log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)) paid.2.2
  have hp := zero_lt_one.trans (R.family.path.levels.fits.delayed (m r))
  rw [Real.rpow_one,←pow_succ,Real.log_pow] at log
  change _ ≤ ((t:ℝ)+1)*(2+Real.log (hat (m r)))
  push_cast at log
  linarith only [log,(Nat.cast_nonneg t : 0≤(t:ℝ))]

end YM.Integration.WilsonPositionProgramTrialCollarKinetic
end
