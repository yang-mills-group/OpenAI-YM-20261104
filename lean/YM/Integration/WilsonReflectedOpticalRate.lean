import YM.Integration.WilsonReflectedRelativeDate
import YM.Integration.WilsonAddressedCollarWindow
/-! The first purchased physical berth has a polynomial upper scale ratio
and pays the physically rescaled signed singleton defect for every nearby
reporting mesh. The exponent is selected before the cutoff and period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOpticalRate
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedReporters WilsonInvariantActionPosition
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "a₀" => (C₀).S.a
local notation "s₀" => (C₀).S.scale
local notation "H₀" => R.family.path.levels.clock.hatBeta

def depth (q B d:ℕ):ℕ:=16*(q+B*(d+1))

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (q B d:ℕ){η:ℝ}(room:0<η):∀ᶠ f:ℕ in atTop,
    let t:=depth q B d
    let K:=berth R t f
    f<K ∧ (H₀ f)^t≤a₀ f/a₀ K ∧ a₀ f/a₀ K≤(H₀ f)^t*(H₀ f)^η ∧
      ∀j,a₀ j/a₀ f≤(H₀ f)^B →
      (a₀ j/a₀ f)^d*hike (C₀) K f rate*(1+4*stock (C₀) K)*stretch R (1/32) j K≤
        4*((H₀ f)^q)⁻¹:=by
  let t:=depth q B d
  obtain ⟨first,account⟩:=eventually_atTop.mp (WilsonReflectedRelativeDate.account R)
  filter_upwards [eventually_ge_atTop first,WilsonAddressedCollarWindow.original R simple slow t room] with f due window
  let K:=berth R t f
  change f<K ∧ _ ∧ _ ∧ _;refine ⟨window.1,window.2.1,window.2.2,?_⟩
  intro j near
  let H:=H₀ f
  have one:1≤H:=(R.family.path.levels.fits.delayed f).le
  have hp:0<H:=zero_lt_one.trans_le one
  have logH:0≤Real.log H:=Real.log_nonneg one
  have a:=Real.log_le_log (div_pos ((C₀).S.a_pos j) ((C₀).S.a_pos f)) near
  rw [WilsonReflectedRelativeDate.ratio,Real.log_pow] at a
  have b:=Real.log_le_log (pow_pos hp t) window.2.1
  rw [WilsonReflectedRelativeDate.ratio,Real.log_pow] at b
  have dj:0≤(d:ℝ)+1/32:=by positivity
  have tval:(t:ℝ)=16*((q:ℝ)+(B:ℝ)*((d:ℝ)+1)):=by unfold t depth;push_cast;rfl
  have limit:((d:ℝ)+1/32)*B+q≤(t:ℝ)/16:=by rw [tval];nlinarith only [(Nat.cast_nonneg B : (0:ℝ)≤B)]
  have combine:=mul_le_mul_of_nonneg_right limit logH
  have prev:=mul_le_mul_of_nonneg_left a dj
  apply (account K (due.trans window.1.le) d j f window.1).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num:0≤(4:ℝ))
  change Real.exp _≤(H^q)⁻¹
  rw [←Real.exp_log (pow_pos hp q),←Real.exp_neg,Real.log_pow]
  apply Real.exp_le_exp.mpr
  change (d+1/32:ℝ)*(s₀ f-s₀ j)≤((d+1/32:ℝ))*((B:ℝ)*Real.log H) at prev
  change (t:ℝ)*Real.log H ≤ (C₀).S.scale K - (C₀).S.scale f at b
  linarith only [prev,b,combine]

end YM.Integration.WilsonReflectedOpticalRate
end
