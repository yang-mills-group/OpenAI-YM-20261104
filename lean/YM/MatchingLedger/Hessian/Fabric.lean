import YM.MatchingLedger.Hessian.Leaf
import YM.MatchingLedger.Hessian.Travel

/-!
# Spectral calibration on the actual rep (and soon regardless of rendering)

Keeps Rep.v terms out of measuredAction. Does not assume exact Fourier diagonalization; actual
cost exact incl affinity & expenditure. This is *approximate* even before moving to PT.
Statement and leverage also hold at period-dependent `p`, including all-active labels. Bring
own verified strip width (eventually prove with q^−...). This is not a hypothesis concerning β
of a second representation. Prefer inclusive n and fixed M cutoff for formal predictions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Lattice Wilson RG Exterior Precision Work.F03 Pert Pert.Kinetic
open AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Finset
variable {n:Side} {G:Gauge} (R : Rep G n) {σ C Λ δ z:ℝ} (h : R.Lawful σ C Λ δ z) (hG:G.Simple)
   (hn:4≤ n.val) (c:G.Color) (hc:‖c‖=1)
local notation "A" => R.activities
local notation "p" => R.p
local notation "q" => fuel n
local notation "m" => Full.mesh n

def flame := angle (spanB c R.path h.paths hn R.beta + (1/2:ℝ) • leafB c R.activities)
def heftFare (k:BudgetPoint)(β C Λ δ:ℝ):= spanPay C Λ β+ paper k * δ /2
lemma symmetry (x y:Site n) : flame R h hn c x y = flame R h hn c y x:= angle_sym ..
include hG hc
lemma pulse_flame (v:Floor n): pulse (flame R h hn c) v v= meterK R (surf c v):= by
    unfold flame; rw [pulse_angle]; unfold pulse; rw [utter_plus,utter_scale, show utter (spanB c R.path h.paths hn R.beta) (spur v v)= _ from span_sampling_all (hc:=hc) c R.path h.paths hn R.beta v, show utter (leafB c A) (spur v v)=_ from leaf_identity c A hc hG h.labels v]; unfold meterK; ring
lemma flame_price {r:ℝ} (hr:0≤r) (hx:r≤1)(hs:r≤σ)(hz:r*(6*((p).B:ℝ)+2) ≤ (p).supportExponent/2) : paid (flame R h hn c) r ≤ fuel n * heftFare p R.beta C Λ δ:= by
    unfold flame; apply (paid_angle ..).trans ((paid_add ..).trans ?_)
    rw [paid_scale,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]; exact (add_le_add (span_fee (hc:=hc) c R.path h.paths hn hr hx hs _) (mul_le_mul_of_nonneg_left (leafy c (A) hc hG h.labels hr hz).2 (by norm_num : (0:ℝ) ≤ 1/2))).trans_eq (by unfold heftFare; ring)
lemma plume : ‖pulse (flame R h hn c) 1 1‖ ≤ m^3*(geomE p /2)*(q*δ):= by
    unfold flame; rw [pulse_angle, pulse,utter_plus,utter_scale,show utter (spanB c R.path h.paths hn R.beta) (spur 1 1)=0 from span_plain (hc:=hc) c R.path h.paths hn R.beta,zero_add,norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; exact (mul_le_mul_of_nonneg_left (wraps c A hc hG h.labels hn) (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)

lemma wind : ‖(∑ b:Bool,pulse (flame R h hn c) (amp b) (amp b))- R.beta*purchase n‖ ≤ q*m^3*billTotal p σ C Λ R.beta δ := by
    have he(b:Bool) : surf c (amp b)= rowWave (n:=n) c b:= by ext1 i; rw [surf_apply c _ i.1 i.2]; unfold rowWave Pert.Kinetic.wave amp; split_ifs; rfl; exact (zero_smul ..).symm
    simp_rw [pulse_flame R h hG hn c hc,he]
    -- adaptation of branch control. Need it for the given rep without comparison to another. no affine seam assumption here.
    let u : Directions G n:= rowWave c true
    have hb := sum_rates h.paths hn hc R.beta; have ht(b:Bool):= frequencyE (n:=n) h.labels hG c hc b 0 1 hn
    unfold meterK; simp_rw [Finset.sum_add_distrib]; rw [add_sub_right_comm,show R.beta*purchase n=R.beta/2* (Fintype.card (Site n):ℝ)*(4*Real.sin (Full.mesh n/2)^2) from by unfold purchase fuel eigen; ring]
    apply (norm_add_le ..).trans; refine (add_le_add (show _≤_ from hb) ?_).trans_eq (show _+(q*m^3 * (geomE p * δ))=_ from by unfold fuel billTotal; ring) -- unify
    rw [← Finset.sum_div,Fintype.sum_bool,norm_div,Real.norm_of_nonneg (zero_le_two: (0:ℝ)≤2)]; exact (div_le_div_of_nonneg_right ((norm_add_le ..).trans (add_le_add (ht true) (ht false))) zero_le_two).trans_eq (by unfold fuel; ring)
lemma leafy_bill {r:ℝ} (M:ℕ) (hr:0<r) (hx:r≤1)(hs:r≤σ)(hz:r*(6*((p).B:ℝ)+2) ≤ (p).supportExponent/2):
    ‖listen M (flame R h hn c) - R.beta‖ ≤ 2*tone*(royalty r M*heftFare p R.beta C Λ δ + m*(billTotal p σ C Λ R.beta δ + geomE p*(δ/2))) := by
    have hh := flame_price R h hG hn c hc hr.le hx hs hz; have hp : 0 ≤ heftFare p R.beta C Λ δ := nonneg_of_mul_nonneg_right ((paid_nn ..).trans hh) (fuel_pos n) -- orientation
    have hU : 0 ≤ royalty r M := by unfold royalty; positivity
    refine flattened hn (flame R h hn c) M (mul_nonneg hU hp) ?_ ((wall hn (flame R h hn c) M hr).trans ((mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg _) hU)).trans_eq (by ring)))
    rw [swing_bill,sub_right_comm]; exact (norm_sub_le ..).trans ((add_le_add (wind R h hG hn c hc) (plume R h hG hn c hc)).trans_eq (by ring))

-- link to all-direction tangent Hessian via pole cancellation along surface directions. Uniformity of
-- price in period will come from pricing BOTH sides. Do not try to use this limit interchangeably with volume.
lemma surf_tangent (u : Floor n) : Tendsto (fun t:ℝ=>measuredAction R (line (surf c u) t)/t^2) (𝓝[≠] 0) (𝓝 (pulse (flame R h hn c) u u)):= by
  let L:= surf c u; let r:ℝ:= (p).threshold / (1+ ‖u‖)
  have hr:0<r:= by unfold r; positivity [(p).threshold_pos]
  -- calibrate with norm at support o; Adapt `Kinetic.unscale`
  have ht : 0<1+‖u‖:= by positivity
  have hB (o): (p).dirBound o (r • L):= by
    have he : ((1+‖u‖)/(p).threshold)⁻¹= r:= by rw [inv_div]
    rw [← he]; apply loose_dir («p»:=R.p) o L ht 0 (Nat.zero_le _); intro z
    rw [pow_zero,mul_one]; exact (surf_norm c hc ..).trans ((norm_le_pi_norm u z.1).trans (le_add_of_nonneg_left zero_le_one))
  have H0 := additive_limit h.labels hG _ hB; let U:=surf c u; let V:=line U
  have he : Tendsto (fun t : ℝ=>t/r) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_inf.2 ⟨?_,?_⟩
      · exact ((continuous_id.div_const _).tendsto' 0 0 (zero_div _)).mono_left nhdsWithin_le_nhds
      exact tendsto_principal.mpr ((show ∀ᶠ z : ℝ in 𝓝[≠] 0, z ≠ (0:ℝ) from self_mem_nhdsWithin).mono fun t ht' => div_ne_zero ht' hr.ne')
  have H t : line (r • L) (t/r) = line L t := by dsimp only [line]; rw [smul_smul,div_mul_cancel₀ _ hr.ne']
  have ha := ((H0.1.comp he).mul_const (r^2)⁻¹).congr (f₂:=fun t:ℝ=>R.activities.additive R.p (line L t)/t^2) (by intro t; dsimp only [Function.comp_apply]; rw [H];field_simp)
  have hea(i): logHessian (R.activities.E i) (r • L) (r • L) /2 = r^2*(logHessian (R.activities.E i) L L/2) := by
      simp only [hessian_eq,map_smul,smul_apply,smul_eq_mul,sq]; ring
  simp_rw [hea, tsum_mul_left] at ha
  have hh : (r ^ 2 * (∑' (x : ℕ), logHessian (R.activities.E x) L L / 2)) * (r^2)⁻¹ = Eread («A»:=R.activities) L/2 := by unfold Eread; rw [tsum_div_const]; field_simp
  rw [hh] at ha; rw [pulse_flame R h hG hn c hc u]
  refine Tendsto.congr' ?_ ((multi_tangent h.paths R.beta L).add ha)
  filter_upwards [(rays_free (G:=G) R.p.threshold R.p.threshold_pos L).filter_mono nhdsWithin_le_nhds] with t ht
  unfold measuredAction
  change ((R.beta*(_)+(_))/t^2 + _/t^2)= (_+ (A).additive p (line L t))/t^2
  rw [PhysicalNext.Repeat.Pane.crystalline _ _ _ _ _ ht]; ring

-- line small, eval = exp. Surfaces avoid any scalar sign-change convention. Useful also at u=0
omit hG hc in
lemma eval_asym (v:Directions G n) : ∀ᶠ t : ℝ in 𝓝 0,
    Real.log (R.eval (line v t)) = R.v * fuel n - measuredAction R (line v t):= by
    filter_upwards [rays_free _ (p).threshold_pos v] with t ht
    rw [RG.Rep.eval,Activities.gas_one _ _ ht,mul_one,Real.log_exp]
    unfold RG.Rep.exponent fuel measuredAction; ring

end YM.MatchingLedger.Spring
