import YM.SignedWilsonExpansion.Chron.Telescope
import YM.TraceExtension.Atlas.Sink
import YM.Pert.Asymptotics.RawAxis
/-! Shared asymptotic currency. Does not define t from C. -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Fire
open Function Filter Asymptotics Gauge Wilson RG Real
open Trace.Pilot Purchases UVClock Schedules WilsonCoeffUV.Bank PathCost
open Commission Purchases.HalfRoof.Minty
open scoped Classical BigOperators Topology
variable {G:Gauge} {ι : Type*} (K:Levels G) (h:G.Simple)
abbrev cck (G:Gauge)(x:ℝ) := βClock G id x
abbrev needle (G:Gauge):ℝ→ℝ := mark (cck G)
include h
theorem implicit_clock : Coupling G (needle G) :=by
  let u:=cck G; have hp:Rise u trail:= radius_clock (ρ:=id) h tendsto_id
  have v := hp.eventually_gt_atTop 0; refine ⟨v.mono (fun i h=> inv_pos.mpr (sqrt_pos.mpr h)), tendsto_const_nhds.congr' (?_) ⟩; filter_upwards [v] with i hi; change _=LogV i * ( sqrt (u i) )⁻¹^2; rw [inv_pow,sq_sqrt hi.le,← div_eq_mul_inv, eq_div_iff hi.ne']; change _*( G.slopeConstant * LogV i ) = _; rw[←mul_assoc,inv_mul_cancel₀ (slopeConstant_pos h).ne', one_mul]
theorem coupling (v:ℝ→ℝ)(p:Coupling G v): IsEquivalent trail v (needle G):=by
  let W:= needle G; let q:= implicit_clock h; have hn: G.slopeConstant⁻¹≠0:=inv_ne_zero (slopeConstant_pos h).ne'; have he:= p.running.div q.running hn; rw [div_self hn] at he; apply isEquivalent_of_tendsto_one; have ht:Tendsto LogV trail atTop:= Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hx:Tendsto (fun i=> ( v i/ W i)^2 ) trail (𝓝 1):=by refine he.congr' ?_; filter_upwards [ht.eventually_gt_atTop 0] with i hi; change LogV i * v i ^ 2/(LogV i * (W i)^2)=_; rw [mul_div_mul_left _ _ hi.ne',div_pow]
  have hu:= hx.sqrt; rw [sqrt_one] at hu; exact hu.congr' ( ( p.positive.and q.positive ).mono (fun i hi=> sqrt_sq (div_nonneg hi.1.le hi.2.le) ) )
theorem from_timer (v:ℝ→ℝ)(p:IsEquivalent trail v (needle G)): Coupling G v:=by
  let u:=needle G; let q:= implicit_clock h
  constructor
  · have hp: Tendsto (v/u) trail (𝓝 1):=( isEquivalent_iff_tendsto_one ( q.positive.mono fun i h=>h.ne' ) ).mp p; filter_upwards [ hp.eventually ( lt_mem_nhds zero_lt_one ), q.positive ] with i hi hv; exact pos_of_mul_pos_left ( by change 0<(v i)*(u i)⁻¹; rw [ ← div_eq_mul_inv ]; exact hi ) (inv_nonneg.mpr hv.le) -- lemma check name
  · exact (( IsEquivalent.mul (IsEquivalent.refl (u:=LogV)) ( p.pow 2 ) ).symm.tendsto_nhds q.running ) -- likely arg names
lemma owns_clock {ι:Type}{L:Filter ι} {r:ι→ℝ}(p:Tendsto r L Trace.Pilot.trail){U:ℝ→ℝ}(hU:Coupling G U): (fun i=> U (r i)^2) ≤ᶠ[L] payD (cck G ∘ r) (-1/2) :=by
   have hr:Rise (cck G ∘r) L:= radius_clock h p
   apply Integration.Exporter.Loans.Consume.tuck (β:= -1) hr _ (by norm_num)
   have he:= ((coupling h _ hU).isBigO.comp_tendsto p); have hu:= Consume.power (n:=2) ( A:= (U ∘r) ) ( he.trans ( penMap hr ( EventuallyEq.rfl ) ) ); norm_num at hu; exact hu
end YM.SignedWilsonExpansion.Fire
