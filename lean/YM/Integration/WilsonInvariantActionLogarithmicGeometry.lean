import YM.Integration.WilsonInvariantActionSeparatedWindow

/-! The physical sample's two actual ancestor sites already clear the
separated transfer window on the logarithmic manuscript clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionLogarithmicGeometry
open Filter Function Set Finset Real MeasureTheory Lattice Wilson RG Source Spec
open Next.Rank PhysicalNext.Repeat.Legato RG17 FullVolume Extraction.Order RGComparison.Core16 Table Climb Trace.Pilot Next.UVStress
open WilsonInvariantActionSeparatedCells
open private logarithms from YM.Integration.WilsonInvariantActionSeparatedWindow
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

include pace in
theorem original {B:ℕ} (large:17≤B) (φ:Test 2):
    let m:=WilsonMeasuredWindow.stop (A) simple B
    ∀ᶠ r in trail,∀(hr:0<r) N per (h:m r≤N)(x:Fin 2→Site (R.family.side N per)),
    WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0 →
    ((A).budget (m r)).B^8≤gap R.family h x ∧ (gap R.family h x:ℝ)≤β (m r):=by
  let m:=WilsonMeasuredWindow.stop (A) simple B
  obtain ⟨l,u,lp,up,sites⟩:=WilsonInvariantActionSeparatedCells.filed R.family φ
    φ.hasCompactSupport φ.tsupport_subset (Subset.rfl)
  let c:=l/2
  have cp:0<c:=half_pos lp
  obtain ⟨grows,window⟩:=WilsonFundedMeasuredWindow.all_radii R pace simple (B:=B) (by omega)
  have upper:=grows.eventually (logarithms R simple (B+1) (inv_pos.mpr (by positivity :0<u+1)))
  have lograte: Tendsto (fun r=>Real.log (β (m r))) trail atTop:=
    Real.tendsto_log_atTop.comp ((Station.hat_rate (A) simple).comp grows)
  filter_upwards [sites,upper,lograte.eventually_ge_atTop (max 1 (1/c)),
    (eventually_le_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with r placed bound scale small
  intro hr N per hk x live
  let j:=m r;let t:=Real.log (β j);let L:=RG16.Lambda (A) j
  have t1:1≤t:=(le_max_left ..).trans scale
  have z1:1≤L:=by change 1≤2+t;linarith
  have ld:1≤c*L:=by
    have z:1/c≤t:=(le_max_right ..).trans scale
    have room:1≤t*c:=(div_le_iff₀ cp).mp z
    change 1≤c*(2+t);linarith only [room,cp]
  have climb:1≤c*L^B:=
    ld.trans (mul_le_mul_of_nonneg_left (by simpa only [pow_one] using
      (pow_le_pow_right₀ z1 (show 1≤B by omega))) cp.le)
  have cap:((((A).budget j).B^8:ℕ):ℝ)≤c*L^B:=by
    have core:(⌈t^2⌉₊:ℝ)≤L^2:=by change _≤(2+t)^2;linarith only [(Nat.ceil_lt_add_one (sq_nonneg t)).le,t1]
    change ((⌈t^2⌉₊^8:ℕ):ℝ)≤c*L^B;rw [Nat.cast_pow]
    calc
      _≤(L^2)^8:=pow_le_pow_left₀ (Nat.cast_nonneg _) core 8
      _=L^16:=by rw [←pow_mul]
      _≤ L^16*(c*L):=by simpa only [mul_one] using (mul_le_mul_of_nonneg_left ld (pow_nonneg (zero_le_one.trans z1) 16))
      _=c*L^17:=by ring
      _≤c*L^B:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ z1 large) cp.le
  obtain ⟨low,hi⟩:=window r hr small
  obtain ⟨lo,top⟩:=placed hr j N per hk x live
  have larget: c*L^B≤c*(r/a j):=mul_le_mul_of_nonneg_left low cp.le
  have lg:2*(c*(r/a j))≤(gap R.family hk x:ℝ)+1:=by
    simpa only [c,←mul_div_assoc] using (show 2*((l/2)*r/a j)≤_ by
      convert lo using 1;ring)
  have charged:((((A).budget j).B^8:ℕ):ℝ)≤gap R.family hk x:=by
    linarith only [cap,larget,climb,lg]
  have lim:(u+1)*L^(B+1)≤β j:=by
    have refund:L^(B+1)≤(u+1)⁻¹*β j:=bound
    have own:=mul_le_mul_of_nonneg_left refund (le_of_lt (by positivity :0<u+1))
    simpa only [←mul_assoc,mul_inv_cancel₀ (ne_of_gt (by positivity :0<u+1)),one_mul] using own
  refine ⟨by exact_mod_cast charged,?_⟩
  calc
    _≤u*(r/a j)+1:=by simpa only [mul_div_assoc] using top
    _≤u*L^(B+1)+L^(B+1):=add_le_add (mul_le_mul_of_nonneg_left hi up.le) (one_le_pow₀ z1)
    _=(u+1)*L^(B+1):=by ring
    _≤β j:=lim

end YM.Integration.WilsonInvariantActionLogarithmicGeometry
