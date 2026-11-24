import YM.Integration.WilsonInvariantActionSeparatedCells
import YM.Integration.WilsonInvariantActionPromotedQuota

/-! Admission of the actual two-site signed test at the finer reporting berth.
Its distance may be an arbitrary fixed power of the coupling budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionSeparatedWindow
open Function Filter Set MeasureTheory Lattice Wilson RG Source Marker Extraction Spec
open Next.Rank PhysicalNext.Repeat.Legato RG17 FullVolume Extraction.Order RGComparison.Core16 Table Climb Trace.Pilot Next.UVStress
open WilsonInvariantActionPosition WilsonInvariantActionSeparatedCells
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

include simple
private lemma logarithms (D:ℕ) {c:ℝ} (hc:0<c):∀ᶠ j:ℕ in atTop,RG16.Lambda (A) j^D≤c*β j:=by
  have grows:=Real.tendsto_log_atTop.comp (Station.hat_rate (A) simple)
  have low:=((Real.isLittleO_pow_exp_atTop (n:=D)).comp_tendsto grows).bound (div_pos hc (pow_pos (by norm_num:0<(3:ℝ)) D))
  filter_upwards [grows.eventually_ge_atTop 1,low] with j large price
  let x:=Real.log (β j)
  have one:1≤x:=large
  have bp:0<β j:=zero_lt_one.trans ((A).fits.delayed j)
  have rate:x^D≤(c/3^D)*β j:=by
    change ‖x^D‖≤(c/3^D)*‖Real.exp x‖ at price
    have ex:Real.exp x=β j:=Real.exp_log bp
    simpa only [ex,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (zero_le_one.trans one) _),
      abs_of_nonneg bp.le] using price
  change (2+x)^D≤c*β j
  calc
    _ ≤ (3*x)^D:=pow_le_pow_left₀ (by linarith) (by linarith) _
    _=3^D*x^D:=mul_pow .. 
    _≤3^D*((c/3^D)*β j):=mul_le_mul_of_nonneg_left rate (by positivity)
    _=c*β j:=by field_simp

private lemma allowance {c:ℝ} (hc:0<c):
    ∀ᶠ k:ℕ in atTop,(((A).budget k).B^8:ℕ)≤c*β k:=by
  filter_upwards [logarithms R simple 16 hc,(Real.tendsto_log_atTop.comp (Station.hat_rate (A) simple)).eventually_ge_atTop 1] with k cash large
  let x:=Real.log (β k)
  have high:1≤x:=large
  have base:(⌈x^2⌉₊:ℝ)≤(2+x)^2:=by
    linarith only [(Nat.ceil_lt_add_one (sq_nonneg x)).le,high]
  change (↑(⌈x^2⌉₊^8:ℕ):ℝ)≤c*β k
  rw [Nat.cast_pow]
  have sold:(2+x)^16≤c*β k:=cash
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) base 8).trans (by rw [←pow_mul];exact sold)

include pace
private theorem units {B:ℕ} (hB:0<B) {s:ℕ} (hs : 1 ≤ s):
    let b:=WilsonMeasuredWindow.stop (A) simple B
    let k:=fun r=>berth R s (b r)
    Tendsto k trail atTop ∧ ∀ᶠr in trail,(β (k r))/2≤r/a (k r) ∧ r/a (k r)≤β (k r)^(s+3):=by
  let b:=WilsonMeasuredWindow.stop (A) simple B
  let k:=fun r=>berth R s (b r)
  obtain ⟨grow,win⟩:=WilsonFundedMeasuredWindow.all_radii R pace simple hB
  have beyond:Tendsto k trail atTop:=tendsto_atTop_mono (fun r=>(arrival R s (b r)).1.le) grow
  refine ⟨beyond,?_⟩
  filter_upwards [grow.eventually (WilsonInvariantActionPromotedQuota.retained R simple pace s),
    grow.eventually (logarithms R simple (B+1) (show (0:ℝ)<1 from zero_lt_one)),
    (show ∀ᶠr in trail,0<r from self_mem_nhdsWithin), (eventually_le_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with r cash cheap hr tiny
  let m:=b r;let j:=k r
  have mk:m≤j:=(arrival R s m).1.le
  have b1:1≤β m:=((A).fits.delayed m).le
  have lam:1≤RG16.Lambda (A) m:=by change 1≤2+Real.log (β m);linarith only [Real.log_nonneg b1]
  obtain ⟨wlo,whi⟩:=win r hr tiny
  have origin:1≤r/a m:=(one_le_pow₀ lam).trans wlo
  have step:a j*(β m)^s≤a m:=(arrival R s m).2
  have before:(β m)^s≤a m/a j:=(le_div_iff₀ (R.family.S.a_pos j)).2 (by rw [mul_comm];exact step)
  have uniform:β m≤β j:=WilsonStartup.Timing.hat_mono (A) (G.slopeConstant_pos simple).le mk
  have convert:r/a j=(r/a m)*(a m/a j):=by field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos j).ne']
  constructor
  · calc _≤β m:=by linarith only [cash.1]
         _≤(β m)^s:=by simpa only [pow_one] using pow_le_pow_right₀ b1 hs
         _≤a m/a j:=before
         _≤r/a j:=by rw [convert];exact le_mul_of_one_le_left (div_nonneg (R.family.S.a_pos m).le (R.family.S.a_pos j).le) origin
  · rw [convert]
    have sale:r/a m≤β m:=whi.trans (by simpa only [one_mul] using cheap)
    calc _≤β m*β m^(s+2):=mul_le_mul sale cash.2 (div_nonneg (R.family.S.a_pos m).le (R.family.S.a_pos j).le) (zero_le_one.trans b1)
         _=(β m)^(s+3):=by rw [pow_succ];ring
         _≤(β j)^(s+3):=pow_le_pow_left₀ (zero_le_one.trans b1) uniform _

/-- Before all original finite tori, the marks contributing to the signed
profile have an admissible common separation and aspect ratio at the same
berth used for the two reporting deposits. -/
theorem filed {B:ℕ} (hB:0<B) {s:ℕ} (hs : 1 ≤ s) (φ:Test 2)
    {K:Set (Points 2)} (compact:IsCompact K) (sep:K⊆conf 2) (here:tsupport φ⊆K):
    let m:=WilsonMeasuredWindow.stop (A) simple B
    let k:=fun r=>berth R s (m r)
    ∃ (br:ℕ) (dis:ℝ→ℕ),0<br ∧ Tendsto k trail atTop ∧
       ∀ᶠ r in trail,((A).budget (k r)).B^8≤dis r ∧
       (dis r:ℝ)≤β (k r)^(s+4) ∧
       ∀(hr:0<r) N per (h:k r≤N)(x:Fin 2→Site (R.family.side N per)),
       WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0→
       dis r≤gap R.family h x ∧ gap R.family h x≤br*dis r:=by
  let m:=WilsonMeasuredWindow.stop (A) simple B;let k:=fun r=>berth R s (m r)
  obtain ⟨l,u,lp,up,sites⟩:=WilsonInvariantActionSeparatedCells.filed R.family φ compact sep here
  let c:=l/4;have cp:0<c:=div_pos lp (by norm_num)
  let br:=⌈u/c⌉₊+1;let dis:=fun r:ℝ=>⌈c*(r/a (k r))⌉₊
  obtain ⟨grows,clock⟩:=units R simple pace hB hs
  have growsβ: Tendsto (fun r=>β (k r)) trail atTop:=(Station.hat_rate (A) simple).comp grows
  refine ⟨br,dis,Nat.succ_pos _,grows,?_⟩
  filter_upwards [sites,clock,grows.eventually (allowance R simple (half_pos cp)),growsβ.eventually_ge_atTop (max (2/c) (c+1))] with r geometry rates budget scale
  let j:=k r;let X:=r/a j;let d:=dis r
  have low:β j/2≤X:=rates.1
  have bp:1≤β j:=((A).fits.delayed j).le
  have x0:0≤X:=(by positivity:0≤β j/2).trans low
  have start:2≤c*β j:=(div_le_iff₀ cp).mp (le_trans (le_max_left ..) scale) |>.trans_eq (mul_comm ..)
  have one:1≤c*X:=by linarith only [start,mul_le_mul_of_nonneg_left low cp.le]
  have dd:c*X≤(d:ℝ):=Nat.le_ceil _
  have upper:(d:ℝ)≤c*X+1:=(Nat.ceil_lt_add_one (mul_nonneg cp.le x0)).le
  refine ⟨?_,?_,?_⟩
  · have cash:((((A).budget j).B^8:ℕ):ℝ)≤(d:ℝ):=by
      linarith only [budget,mul_le_mul_of_nonneg_left low cp.le,dd]
    exact_mod_cast cash
  · have warm:c+1≤β j:=(le_max_right ..).trans scale
    have pow1:1≤β j^(s+3):=one_le_pow₀ bp
    change (d:ℝ)≤β j^(s+4)
    calc
      _≤c*X+1:=upper
      _≤c*β j^(s+3)+β j^(s+3):=add_le_add (mul_le_mul_of_nonneg_left rates.2 cp.le) pow1
      _=(c+1)*β j^(s+3):=by ring
      _≤β j*β j^(s+3):=mul_le_mul_of_nonneg_right warm (by positivity)
      _=_:=by rw [pow_succ];ring
  · intro hr N per h x live
    obtain ⟨lo,hi⟩:=geometry hr j N per h x live
    have lX:l*r/a j=4*(c*X):=by dsimp only [c,X];ring
    have sold:(d:ℝ)≤(gap R.family h x:ℝ):=by linarith only [upper,lo,one,lX]
    have brcap:u/c+1≤(br:ℝ):=by
      change u/c+1≤((⌈u/c⌉₊+1:ℕ):ℝ)
      rw [Nat.cast_add,Nat.cast_one];exact add_le_add (Nat.le_ceil _) le_rfl
    have earn:u*X≤(u/c)*(d:ℝ):=by
      calc _=(u/c)*(c*X):=by field_simp
           _≤_:=mul_le_mul_of_nonneg_left dd (div_nonneg up.le cp.le)
    have reach:(gap R.family h x:ℝ)≤(br:ℝ)*d:=by
      calc _ ≤ u*X+1:=by simpa only [X,mul_div_assoc] using hi
           _ ≤ (u/c)*(d:ℝ)+d:=add_le_add earn (one.trans dd)
           _ = (u/c+1)*(d:ℝ):=by ring
           _ ≤ _:=mul_le_mul_of_nonneg_right brcap (Nat.cast_nonneg _)
    exact ⟨by exact_mod_cast sold,by exact_mod_cast reach⟩

end YM.Integration.WilsonInvariantActionSeparatedWindow
