import YM.Integration.WilsonReflectedOpticalStock
import YM.Integration.WilsonReflectedEmbeddedLocations
/-! On the purchased optical berth, the later width and the *number*
of actual transfer dates from the reporter have original before-period
budgets, even when the chosen reporting date moves. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOpticalWidth
open Filter Function Set Lattice RG Wilson Source Extra.Histories PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address Trace.Pilot WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff
open scoped Classical Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family.path.levels.clock
local notation "H₀" => (C₀).hatBeta
local notation "S₀" => R.family.S
local notation "mesh" => (S₀).a

theorem steps {j K:ℕ}(ok:j≤K):((K-j:ℕ):ℝ)*Real.log 2≤(S₀).scale K-(S₀).scale j:=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le ok
  have x:=WilsonReflectedEmbeddedLocations.count R ok 0
  change (((S₀).steps j (j+n-j)).val:ℝ)=_ at x
  rw [Nat.add_sub_cancel_left] at x ⊢
  have pay:(2:ℝ)^n≤(((S₀).steps j n).val:ℝ):=by exact_mod_cast WilsonReflectedOriginalPrefixMesh.dyadic (S₀) j n
  have log:=Real.log_le_log (show 0<(2:ℝ)^n by positivity) (pay.trans_eq x)
  rwa [Real.log_pow,WilsonReflectedRelativeDate.ratio] at log

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(B t:ℕ){η:ℝ}(room:0<η):
    ∃M F:ℝ,0<M ∧ 0≤F ∧ ∀ᶠ f:ℕ in atTop,let K:=berth R t f
    width (C₀) K≤M*(H₀ f) ∧ ∀b,b≤f→mesh b/mesh f ≤ (H₀ f)^B →
      ((K-b:ℕ):ℝ)≤F*width (C₀) K:=by
  let v:=G.slopeConstant
  let T:=(t:ℝ)+η
  let D:=(B:ℝ)+T
  let P:=1+v*T
  let M:=1+|v|+P
  have ve:0≤v:=(Gauge.slopeConstant_pos simple).le
  have te:0≤T:=add_nonneg (Nat.cast_nonneg _) room.le
  have dp:0≤D:=add_nonneg (Nat.cast_nonneg _) te
  have pp:0≤P:=add_nonneg zero_le_one (mul_nonneg ve te)
  have mp:0<M:=by unfold M;positivity
  have log2:0<Real.log 2:=Real.log_pos (by norm_num)
  refine ⟨M,D/Real.log 2,mp,div_nonneg dp log2.le,?_⟩
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t room] with f scales
  let K:=berth R t f
  have hp:1≤H₀ f:=(R.family.path.levels.fits.delayed f).le
  have hpK:1≤H₀ K:=(R.family.path.levels.fits.delayed K).le
  have zp:0<H₀ f:=zero_lt_one.trans_le hp
  have logH:=Real.log_le_self zp.le
  have rel:=Real.log_le_log (div_pos ((S₀).a_pos f) ((S₀).a_pos K)) scales.2.2
  rw [WilsonReflectedRelativeDate.ratio,Real.log_mul (pow_pos zp _).ne' (Real.rpow_pos_of_pos zp _).ne',
    Real.log_pow,Real.log_rpow zp] at rel
  have after:(S₀).scale K-(S₀).scale f≤T*Real.log (H₀ f):=by unfold T;linarith only [rel]
  have slopeBound:=mul_le_mul_of_nonneg_left (after.trans (mul_le_mul_of_nonneg_left logH te)) ve
  have higher:H₀ K≤P*(H₀ f):=by
    have values:H₀ K=H₀ f+v*((S₀).scale K-(S₀).scale f):=by unfold Calendar.hatBeta;dsimp only [v];ring
    rw [values];dsimp only [P];linarith only [slopeBound]
  constructor
  · have h:=le_mul_of_one_le_right (show 0≤1+|v| by positivity) hp
    have paid:=Real.log_le_self (zero_le_one.trans hpK)
    unfold width;dsimp only [M,v] at *;linarith only [paid,higher,h]
  intro b before near
  have total:=steps R (before.trans scales.1.le)
  have prior:=Real.log_le_log (div_pos ((S₀).a_pos b) ((S₀).a_pos f)) near
  rw [WilsonReflectedRelativeDate.ratio,Real.log_pow] at prior
  have lt:Real.log (H₀ f)≤width (C₀) K:=by
    have pay:=Real.log_le_log zp (WilsonReflectedOpticalStock.monotone R simple scales.1.le)
    unfold width;linarith only [pay,abs_nonneg G.slopeConstant]
  have product:((K-b:ℕ):ℝ)*Real.log 2≤D*width (C₀) K:=calc
    _ ≤ D*Real.log (H₀ f):=by unfold D;linarith only [total,prior,after]
    _ ≤ _ :=mul_le_mul_of_nonneg_left lt dp
  exact ((le_div_iff₀ log2).mpr product).trans_eq (by ring)

end YM.Integration.WilsonReflectedOpticalWidth
end
