import YM.Contacts.Bounty.Density
/-!
 # Blueprint for actual and all auxiliary purchases amortized living released.
 L^-1/2 for any profile, τ_in up to actual fine Mind.
 ζ=rank EARLY Request (≥2). λ=x'^{-(ζ+2)}.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Bounty.Trophy.Lore
open AnalyticBridge VerifiedReset Collection Quotes Revest Flute Outlay
open PhysicalNext.Repeat PhysicalNext.Repeat.Roost Terrain
open Function Filter Lattice Wilson RG Pressure Ovens Ovens.Pipes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Org
open UVNext.CouplingReset Push Push.AbsoluteSums Animals Precision RG.Supply Input RG.Shoot PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Next.Scheduling PhysicalNext.ThroughLaunch Time Model Arbor Province.Costing Tucks Milling.Steam
open Pulse ConnectedActivityE6 Testing SectorMeasure Presented Coat Blaze Blaze.March
open Boulevard Poetry Song Deck Trio Slide Push.Uniform
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable (G: Gauge) {M: Metals G}{D:Rolls M.p} (L: Side) {F:Postage} (A:Time.Forecast F) (p:RG.Stage) (U ν v V φ ζ t:ℝ) (l o:ℕ)
abbrev veil (ζ:ℝ) (x:ℝ):ℝ:=x^(-(ζ+2):ℝ)
local notation "d" => (dim l o)
-- implicit.Pay curvature.C constants after.R.
abbrev spanCost (l o:ℕ)(x:ℝ):= Trio.base (dim l o) (radiusB x)
local notation "η" => Height.away p
abbrev owne (A:ℝ) (L:Side) (p:Stage):= Height.away p*((3+A)/ L.val)
-- λ position.B care
abbrev nana (t:ℝ) := (η)*(veil ζ t+veil ζ t)+veil ζ t
abbrev wholeBasis (t:ℝ) :ℝ := (η)*(t^(-(7/16):ℝ)+t^(-(7/16):ℝ))
abbrev oldBasis := wholeBasis
abbrev wageW (l o:ℕ)(x y:ℝ)(p:Stage):ℝ:= (ballCost (spanCost l o x):ℝ) * (wholeBasis p y)+y^(-(7/16):ℝ)
abbrev Tax (i:Stars) (x:ℝ) := (Fintype.card (Site (Trio.fence d (radiusB x) i)):ℝ)
abbrev sheath (x y:ℝ)(i:Stars) := Boulevard.ticket p.order (veil ζ y)+2*( Tax l o i x * nana p ζ y)
def savings (x y:ℝ):= Trio.oroW (Time.probe p) (spanCost l o x) (sheath p ζ l o x y)
def dry (x y:ℝ):= savings p ζ l o x y * Real.exp ((p.supportExponent+3)*Trio.coverTicket d)
def levy (l o:ℕ)(x y:ℝ)(p:Stage):ℝ:= let W:= wageW l o x y p; W+W+∑ i:Stars, |Slide.ray i| *(Tax l o i x *(W+W))
abbrev march (L:Side) := (L.val:ℝ)^(-(1/2):ℝ)
-- Need Pre purchase.Read: C+e below Φ.
def Priced (p:Stage)(L:Side)(v:ℝ):Prop:= brutal p G *owne v L p ≤ march L∧ owne v L p ≤ credit G p/8
lemma pricing: ∃ n:ℕ,∀ L:Side,n≤ L.val→ Priced G p L v:= by
   let c:= (3+v); let a:= Height.away p; let b:= brutal p G; obtain ⟨z,hz⟩:= exists_nat_gt (max ((b*a*c)^2) (a*c/(credit G p /8))); refine ⟨z,fun L hL=>?_⟩; obtain ⟨hf,hV⟩:= max_lt_iff.mp (hz.trans_le (show (z:ℝ)≤ L.val from by exact_mod_cast hL)); let l:=(L.val:ℝ); have hl:0<l:= Nat.cast_pos.mpr L.pos; change b*(a*(c/l))≤ march L ∧ a*(c/l) ≤_; rw [← mul_div_assoc]; refine ⟨?_, (div_le_iff₀ hl).mpr ?_⟩
   · rw [← mul_div_assoc,march,Real.rpow_neg hl.le,← Real.sqrt_eq_rpow]; have hk: Real.sqrt l>0:= Real.sqrt_pos.mpr hl; apply (div_le_iff₀ hl).2; change b*(a*c) ≤ (Real.sqrt l)⁻¹*l; nth_rw 2 [← Real.sq_sqrt hl.le]; apply le_trans (b:=Real.sqrt l) ?_ (le_of_eq (by field_simp)); nlinarith only [hf,Real.sq_sqrt hl.le,hk]
   · rw [mul_comm (_/8:ℝ)]; exact ((div_lt_iff₀ (show 0<credit G p/8 from (by have ht:=credit_pos G p; positivity))).mp hV).le
-- x' output; keep genuine requests interior.
structure Phase (G:Gauge)(L:Side)(p:Stage) (v ℓ U x:ℝ)(l o:ℕ) :Prop where
    sound : Real.exp 1≤x
    forms : 1<betaF G x L
    cover : radiusB (betaF G x L) ≤2*radiusB x
    ν_low : Outlay.ν x ≤ (betaF G x L)^(-(7/16):ℝ) ∧ Outlay.ν (betaF G x L) ≤ incomingE G L x
    tilt (b:ℝ)(h:b∈ Set.Icc ((betaF G x L)/2) (2*betaF G x L))(Δ α:ℝ)(hc:|α| ≤ U)(hu:|Δ-α| ≤ potion x):
      b+Δ ∈ Set.Icc ((1/4:ℝ)*x) (4*x) ∧ |b+Δ| ≤ 4*betaF G x L ∧ |Δ|≤U+1
    octave (B:BudgetPoint)(h:Time.Same p B)(ht:B.threshold ≤ 2*Pressure.fiery G x L)(hp:B.B= radiusB x)(b q K:ℝ)(ha:|b| ≤ 4*betaF G x L)(he:|q|≤ U+1)(hz:0 ≤ K)(hf:K ≤ ConnectedActivityE6.loopBill G L x): let u:=Song.octaveNeed G B p.clip p.width p.paths K b q
      u ≤ betaF G x L ^ (-(7/16):ℝ) ∧ Real.exp (-(p.width/4)*B.B)*u ≤ veil ℓ (betaF G x L)
    folds (B:BudgetPoint)(hh:B.threshold ≤2*Pressure.fiery G x L)(c f:Side)(he:2*spanCost l o x<c.val)(w:ℕ)(hp:w+1 ≤ spanCost l o x)(u:2*w ≤ f.val) (p:Site c)(V:Config G c): Healthy B.threshold (neighbors (spanCost l o x) p) V→ ∃ (z:Site f→G.El)(u':Positions (Uniform.Primary f G)), Boulevard.actual u'=gauge z (Slide.shape (Slide.cognac u) p V) ∧ ‖u'‖+2*Sienna.furl G L x< Sienna.eaves G L x
    loose : Marlin.tithe (2*spanCost l o x) (Lore.levy l o x (betaF G x L) p) (Time.probe p) (Trio.coverTicket (dim l o)) ≤ (betaF G x L)^ (-(1/8):ℝ)
    back (r:ℝ) (hr:0 ≤ r)(hp:r ≤ incomingE G L x): let y:= betaF G x L; let B:= nana p ℓ y+owne v L p*r+Height.away p*dry p ℓ l o x y
      Priced G p L v → B≤Time.credit G p * δE x/4 ∧ Outlay.brutal p G * B ≤ x^(-ℓ)+ march L*r

lemma art (he:0≤U)(hh:2≤ζ) : ∀ᶠ x:ℝ in atTop,Phase G L p v ζ U x l o:= by
   let A:= dim l o; let f x:= betaF G x L; let K x:= fence A (radiusB x); have hm i:= feeStars G L A i; let D:= (-(ζ+2)); let w(x:ℝ):=veil ζ (f x);
   have hb :Rate G L D w:= Rate.power; let C:= credit G p; have hc: 0<C:=credit_pos ..; have hv : Rate G L (-(7/16)) (fun x=> wholeBasis p (f x)):= by exact ((Rate.add (a:=-(7/16)) Rate.power Rate.power).mul_left _);
   have hh': Rate G L (-(7/16)) (fun x=> Lore.levy l o x (f x) p):= by
      let S x:= wageW l o x (f x) p; have hw : Rate G L (-(7/16)) (fun x=> S x+ S x):= by
          have he : Rate G L (-(7/16)) S:= Rate.add ((zero_add (-(7/16:ℝ))) ▸ ((balls G L (Trio.rows G L A|>.2.2.1)).mul hv)) Rate.power; exact he.add he
      refine hw.add (Trio.sparks G L (fun i=>?_)); exact ((zero_add (-(7/16:ℝ))) ▸ ((feeStars G L A i).mul hw)).mul_left _ -- binder
   let h':=savings p ζ l o; let t:=η; have hN: Rate G L D (fun x=> nana p ζ (f x)):= ((hb.add hb).mul_left _).add hb
   have hS : Rate G L D (fun x=> nana p ζ (f x)+ t*dry p ζ l o x (f x)):= by
      unfold dry savings Trio.oroW; refine hN.add ((Trio.sparks G L (fun i=>?_)).mul_right _ |>.mul_left _)
      let hh:= (Trio.rows G L A).2.2.1; let B:=Time.probe p;
      have hx : Rate G L 0 (fun x => Trio.tilt (Time.probe p) (spanCost l o x)):= (Lantern.Bolt.times (Lantern.Bolt.still _) (Lantern.Bolt.nod ((Lantern.Bolt.still 1).joins hh) _)).uses; exact (((zero_add D) ▸ (hx.mul (Rate.add ((hb.mul_left _).mul_right _) (((zero_add D) ▸ ((feeStars G L A i).mul hN)).mul_left _))))).mul_left _
   have hK := Sienna.contraction G L (a:=brutal p G) (b:=1) zero_lt_one hS (show D < -ζ from by unfold D; linarith); let z:=G.slopeConstant*Real.log (L.val:ℝ); have hz:0≤z:=YM.Work.E04.shift_nonneg ..
   have hP := Sienna.contraction G L (a:=1) (show 0< C/8 from by positivity) hS (show D < -(11/10:ℝ) from (by unfold D; linarith));
   let n:= Lore.dim l o; let w0:= Outlay.ν; let F:= (- (7/16):ℝ)
   have hΘ: Rate G L (-(7/16)) (fun x=>Marlin.tithe (2*spanCost l o x) (Lore.levy l o x (f x) p) (Time.probe p) (Trio.coverTicket (dim l o))):= by
      refine ((zero_add F) ▸ ((balls G L ((Trio.rows G L A).2.2.2)).mul hh')).mul_right _
   filter_upwards [hK,hP,hΘ (-(1/8)) (by norm_num),Meadow.steppes G L p (U+1) D (by linarith), (YM.Work.E09.betaF_growth G L).eventually_gt_atTop 1,Trio.pledges G L (spanCost l o) (Trio.rows G L n|>.2.2.1.uses), eventually_gt_atTop (max (Real.exp 1) (8*(z+U+2))),just_near z, Clock.similar_cover 2 one_lt_two, Terrain.δratio (G:=G) (L:=L),(Sienna.contraction G L (a:=2) one_pos (Rate.power (a:= (-(11/10:ℝ)))) (show -(11/10:ℝ) < -(7/16:ℝ) by norm_num))] with x hC hP hL h'₀ hx hF hp hN hK hz' hU
   let y:= f x; have hy:y>1:=hx; have hx': Real.exp 1<x:=lt_of_le_of_lt (le_max_left ..) hp; have hx:1<x:=(Real.one_lt_exp_iff.mpr zero_lt_one).trans hx'; have ht:= Height.away p; have he':x≤ y:= le_add_of_nonneg_right hz;
   have h {x:ℝ} (hx:1<x): δE x=x^ (-(11/10):ℝ) ∧ w0 x ≤ δE x:= by
       have hv: 0 < x:= zero_lt_one.trans hx; have h : δE x=x^(-(11/10):ℝ):= by unfold δE Clock.gap; rw [Real.sqrt_eq_rpow,← Real.rpow_neg hv.le, ← Real.rpow_mul hv.le]; norm_num
       exact ⟨h,h.symm ▸ Real.rpow_le_rpow_of_exponent_le hx.le (by norm_num : -(23/20:ℝ)≤ -(11/10:ℝ))⟩
   have hb : incomingE G L x=δE y:= rfl; have hA : incomingE G L x≤δE x:= (by rw [hb,(h hy).1,(h hx).1]; exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hx) he' (by norm_num));
   refine ⟨hx'.le,hy,?_,⟨?_,hb.symm ▸ (h hy).2⟩,?_,fun B h hu hB b q v Hb hq hv hy=> ?_,hF,(le_abs_self _).trans hL,?_⟩
   · have hx: (radiusB y:ℝ) ≤ 2*(radiusB x:ℝ):= hK (x+z) x hN (Clock.same x); exact_mod_cast hx
   · change w0 x≤ y^F; refine (h hx).2.trans (hz'.trans ((le_of_eq (congr_arg ((2:ℝ)* ·) (hb.trans (h hy).1))).trans ?_)); linarith only [hU]
   · intro b hb Δ α hc hΔ; have hy: potion x≤1:= Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num); have hx₀: |Δ| ≤U+1:= by rw [← sub_add_cancel Δ α]; linarith only [abs_add_le (Δ-α) α,hΔ,hc,hy]
     have he₁:=lt_of_le_of_lt (le_max_right ..) hp; obtain ⟨hh,hg⟩:= abs_le.mp hx₀; obtain ⟨hl,hu⟩:=hb; change (x+z)/2 ≤ b at hl; change b ≤2*(x+z) at hu; change _∧|b+Δ|≤4*(x+z) ∧ _; exact ⟨⟨by linarith,by linarith⟩, abs_le.mpr ⟨by linarith,by linarith⟩,hx₀⟩
   · obtain ⟨hv,hk,-⟩:= h'₀ B hu h.1 h.2.1 h.2.2 hB b q v Hb hq hv hy; exact ⟨hv,hk⟩
   intro r hr hV y B hL
   have h₂:(brutal p G) * (nana p ζ y+ t*dry p ζ l o x y) ≤ x^(-ζ):= le_trans (by simpa only [one_mul] using hC.le) (Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans hx) he' (neg_nonpos.mpr (by linarith)))
   have hu:nana p ζ y+t*dry p ζ l o x y≤ C*δE x/8:= by linarith only [hP,mul_le_mul_of_nonneg_left hA hc.le, show incomingE G L x = y^(-(11/10):ℝ) from hb.trans (h hy).1, (congr_arg (C * ·) (hb.trans (h hy).1) : C * incomingE G L x= C* y^(-(11/10):ℝ))]
   unfold B; constructor <;> nlinarith only [h₂,hu,mul_le_mul_of_nonneg_right hL.2 hr,mul_le_mul_of_nonneg_right hL.1 hr,(mul_le_mul_of_nonneg_left hV hc.le),  mul_le_mul_of_nonneg_left hA hc.le]
end YM.Contacts.Bounty.Trophy.Lore
