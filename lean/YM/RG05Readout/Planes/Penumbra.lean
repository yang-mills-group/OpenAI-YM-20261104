import YM.RG05Readout.Planes.Cuisine
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Replicator shell availability (using genuine estimates). Growth budget after each reserve.At the SAME pre-side floor as other loans. Any C finite.D. -/
variable (hp:Awake D B b d)
local notation "K!"=> C.path.levels.clock.J
local notation "s!"=> C.S.scale
local notation "P!"=> C.path.levels
local notation "Ł"=> fun i:ℕ => (↑((C.S.block i).val):ℝ)
local notation "T!"=> ld C.path.levels
local notation "F"=> powerFare B d
include hp
lemma always (i:ℕ)(hx:b ≤ i):
      1 ≤ B d i ∧ F i ≤ 4*T! i ∧ F (i+1) ≤ 4 * T! i ∧ 2 ≤ T! i:=by
   have ht := hp.toll 0 i (i+1) hx (Nat.lt_succ_self _); have hP:=ht.pos.1; have hQ:=ht.pos.2; have hu:=ht.caps; refine ⟨hQ,?_,?_,?_⟩; all_goals try (unfold powerFare; rw [max_eq_right (by assumption)])
   all_goals linarith only [hP,hQ,hu]
lemma lane_rises : Tendsto (fun i=> (↑((C.S.block i).val):ℝ)) atTop atTop:=by
   let J'(i:ℕ):=((K! (i+1):ℝ)+1); let ε(i:ℕ):= (T! i:ℝ); let t:= Ł
   have ht:Tendsto J' atTop atTop:= tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp ((C.path.levels.fits.deep).comp (tendsto_add_atTop_nat 1)))
   have hv(i):ε i ^ J' i= (Ł i):=by unfold ε J' ld Copper.lamp; rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ 1 (by positivity),Real.rpow_one];
   apply tendsto_atTop_mono' atTop (f₁:=fun i=> (2:ℝ)^J' i) ?_ ((tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num:(1:ℝ)<2)).comp ht)
   filter_upwards [eventually_ge_atTop b] with i hi; change _ ≤ Ł i; rw [← hv]; exact Real.rpow_le_rpow zero_le_two (always hp i hi|>.2.2.2) (by unfold J'; positivity)

omit hp in
lemma fur_gain (η:ℝ)(hv:0<η):∀ᶠ i:ℕ in atTop,T! i ≤ Ł i ^ η:=by
   have ha: Tendsto (fun i : ℕ=> ((((P!).clock.J (i+1)):ℝ)+1)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp ((P!).fits.deep.comp (tendsto_add_atTop_nat 1))))
   filter_upwards [ha.eventually (ge_mem_nhds hv)] with i hi; exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (C.S.block i).property) (by rwa [one_div])
omit hp in
lemma small_tol : ∀ᶠ i in atTop,tolerance C i ≤ 2* ((Ł i) ^ (-(1:ℝ)/4)):=by
   filter_upwards [fur_gain (C:=C) (1/8) (by positivity)] with i hi; unfold tolerance; have hK: 1≤ (Ł i):=by show (1:ℝ)≤ ((C.S.block i).val:ℝ); exact_mod_cast (C.S.block i).property
   have ht : trim (C.S.block i) ≤ Ł i ^ (-(1:ℝ)/4):= Real.rpow_le_rpow_of_exponent_le hK (by linarith) -- edit
   have hz: T! i * (Doors.rate (C.S.block i)) ≤ Ł i ^ (-(1:ℝ)/4):=by
      apply (mul_le_mul_of_nonneg_right hi (Doors.rate_pos _|>.le)).trans
      unfold Doors.rate; rw [← Real.rpow_add (by positivity)]; apply Real.rpow_le_rpow_of_exponent_le hK; linarith
   rw [two_mul];exact add_le_add ht hz
lemma service_fine : ∀ᶠ i:ℕ in atTop, sufficient C i (powerFare B d i) ∧ grow (powerFare B d (i+1)) ≤ Ł i :=by
   let x:= Ł; let z(u:ℕ):=x u ^(-(1/16:ℝ))
   have ht:Tendsto z atTop (𝓝 0):=(tendsto_rpow_neg_atTop (by norm_num:(0:ℝ)<1/16)).comp (lane_rises hp) 
   filter_upwards [eventually_ge_atTop b,fur_gain (C:=C) (1/16) (by positivity),small_tol (C:=C), ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4096))] with i hi hg hl hx
   obtain ⟨hQ,hB,hP,he⟩:=always hp i hi; let a:= powerFare B d; let K:ℝ:=x i^(1/16:ℝ); have hc: 0< x i:=by unfold x; positivity
   have hA : 1 ≤ a i:=by unfold a powerFare; rw [max_eq_right hQ]; linarith only [hQ]
   have hk:0 < K:= Real.rpow_pos_of_pos hc _; have hv: z i= K⁻¹:=Real.rpow_neg hc.le (1/16:ℝ); have hstep: a i ≤ 4*K:= hB.trans (mul_le_mul_of_nonneg_left hg (by norm_num))
   have hstep':a (i+1)≤4*K:=hP.trans (mul_le_mul_of_nonneg_left hg (by norm_num))
   change a i≤_ at hstep; change T! i≤K at hg; have hxK: K^16=x i:=by unfold K; rw [←Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
   change z i ≤_ at hx; rw [hv,← one_div, div_le_iff₀ hk] at hx; have hk' : 4096 ≤ K:=by linarith only [hx]
   have hδ: (Ł i)^(-(1:ℝ)/4)=(K⁻¹)^4:=by unfold K; rw [inv_pow,←Real.rpow_natCast,← Real.rpow_mul (by positivity)]; rw [neg_div,Real.rpow_neg hc.le]; norm_num
   rw [hδ] at hl; constructor
   · refine (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hA) hstep 3) (by positivity)) hl (dwindles ..) (by positivity)).trans ?_; -- right
     field_simp; linarith only [hk']
   change grow (a (i+1)) ≤ x i; unfold grow; rw [← hxK]; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold a powerFare; positivity) hstep' 2) (by positivity)).trans
   calc 4*(4*K)^2 ≤ K^3:= by nlinarith only [mul_le_mul_of_nonneg_right (show 64 ≤ K by linarith) (sq_nonneg K)]
        _ ≤ K^16:= pow_le_pow_right₀ (by linarith) (by norm_num)

end YM.RG05Readout.Planes
