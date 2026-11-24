import YM.RGComparison01.Marks.Finance
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
/-!
# Financial estimates after the log.
 P stage, estimates at BOTH scaled Booth and Keeper. Keep powers until merging
 with actual masks and analytic repr estimates. -/
namespace Foreman
open ConnectedActivityE6.Blaze.March Captain
open Baked Palette Pillow Resin
local notation "X₀" => H.faresP
local notation "K₁" => (Q.costs L μ 1 s 0)
local notation "xp" => (radiusB s)
section calculus
lemma additive {p:ι→Support c}{F' Y b m:ι→ℝ}{v X D d:ℝ} (h:Ac.Hit p n (tariff F' b m D) v X)(he:Ac.Hit p n (tariff Y b m D) v d):
   Ac.Hit p n (tariff (fun i=>F' i+Y i) b m D) v (X+d):=by intro i; convert budget_plus (h i) (he i) using 1; ext z; unfold tariff; by_cases hz:i∈ p z <;> simp [add_mul,hz]
lemma chew {α w:ℝ} : Trees.degreePrice n α w= Trees.degreePrice n 1 w * α := by unfold Trees.degreePrice Trees.stretch; ring
lemma collar_price {i:ℝ} : Geo G L (fun s=> collars G i s j k):= by
   have he : Geo G L shiftG:= (Geo.fixed 4).times (((Geo.fixed 2).times Geo.radii).joins (Geo.fixed _))
   exact (he.power _).times (Geo.fixed _)
lemma degreeCost (δ:ℝ) : Geo G L (fun s=> Trees.degreePrice (radiusB s) 1 δ):=by
   have h:= (Geo.balling (f:=fun x : ℝ=>radiusB x) (G:=G) (L:=L) Geo.radii); unfold Trees.degreePrice Trees.stretch; simp only [div_eq_mul_inv,mul_one]; exact (Geo.fixed _).times (h.times (Geo.fixed _))
def Width (Q:ConnectedActivityE6.Target G P) (_L:Side) := -(Q.rate/2)
def zephyr (Q:ConnectedActivityE6.Target G P) (L:Side) (s:ℝ) := betaF G s L ^ Width Q L
lemma width_power (Q:ConnectedActivityE6.Target G P)(L:Side): 0 < Width Q L:= by unfold Width; linarith [Q.stop]
lemma booked (Q:ConnectedActivityE6.Target G P)(L:Side)(k:ℕ):∃ m:ℕ, ∀ᶠ s in atTop,
    Height.grow G L s^k ≤ zephyr Q L s^m:= by
  obtain ⟨m,hm⟩:= exists_nat_gt ((3/8*k:ℝ)/Width Q L); refine ⟨m,?_⟩
  filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx
  unfold zephyr Height.grow; simp_rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hx)] -- rpow_prec
  exact Real.rpow_le_rpow_of_exponent_le hx ((show (3/8:ℝ)*k≤Width Q L*m from (((div_lt_iff₀ (width_power Q L)).1 hm).le.trans_eq (mul_comm _ _))))

lemma slides_form (Q:ConnectedActivityE6.Target G P) (t : ℝ) : Slides Q t = Slides Q 1 * t := by unfold Slides treeYield; ring
lemma gen_form (Q:ConnectedActivityE6.Target G P)(j k:ℕ)(t v:ℝ): Geno Q j k t v=Geno Q j k 1 1*v*t:=by unfold Geno treeYield; ring
-- inverse polynomial choice
lemma reduces {f':ℝ→ℝ} (h:Geo G L f')(v:ℝ)(hv:0<v) : ∃ u U:ℝ→ℝ,Geo G L u∧Geo G L U∧ ∀ s:ℝ, 0 < u s ∧U s= (u s)⁻¹ ∧ |f' s| * u s ≤ v:= by -- variable f'
  let e s:=1+|f' s|; have he s:1≤e s:= le_add_of_nonneg_right (abs_nonneg _); let u s:= v/(e s)
  have hQ s: 0 < u s:= div_pos hv (zero_lt_one.trans_le (he s))
  refine ⟨u,fun s=> (u s)⁻¹,(Geo.fixed v).small ?_, ?_, fun s=> ⟨hQ _,rfl,?_⟩⟩
  · filter_upwards with x; rw [abs_of_pos (hQ _), abs_of_pos hv]; exact div_le_self hv.le (he x)
  · have hX := ((Geo.fixed 1).joins h.mean).times (Geo.fixed v⁻¹); unfold u e at *; simpa only [inv_div,div_eq_mul_inv,_root_.mul_inv_rev,inv_inv] using! hX
  unfold u; rw [← mul_div_assoc]; apply (div_le_iff₀ (zero_lt_one.trans_le (he _))).2; exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hv.le).trans_eq (mul_comm (e s) v)
end calculus
section spline
variable (Q:ConnectedActivityE6.Target G P)
-- terms from payments; Ready rooted endpoints. c slope after root guard
structure Coins (Q:ConnectedActivityE6.Target G P)(L:Side)(μ x:ℝ)(j k:ℕ)(v w E B c m δ:ℝ) :Prop where
   first : zephyr Q L x*m^j*(Q.costs L μ 1 x 0).rootHit + (E*wageIn Q L x*v) + wageIn Q L x*v ≤ w
   born : 0<w
   sits : 0<v
   boots : degreePrice (radiusB x) w Q.δ ≤ 1/2
   rate_r : 0 ≤ wageIn Q L x
   next : max (Slides Q w) (Geno Q j k w B) ≤ c
   short : 0 < c
   more : 16*c≤1/2
   heat : degreePrice (radiusB x) c δ ≤1/2
   restore : degreePrice (radiusB x) (16*c) δ ≤1/2

lemma wage_in_pos (L:Side)(x:ℝ) : 0 ≤ wageIn Q L x:= by
   have hu:= Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr Q.usable)
   have hp : 0≤1 - Real.exp (-Q.ε):= by linarith; -- positive
   unfold wageIn Footprint.payment Footprint.degreeIncome
   have h:= Q.usable; positivity

lemma capital (Q:ConnectedActivityE6.Target G P)(L:Side){f g:ℝ→ℝ} (h:Geo G L f)(hp:Rate G L 0 g) (hm : 0<μ) (j k:ℕ) {e δ:ℝ} : ∃ v w c U:ℝ→ℝ, Geo G L v ∧Geo G L w ∧Geo G L c∧Geo G L U ∧ ∀ᶠ x in atTop, U x=(v x)⁻¹ ∧ Coins Q L μ x j k (v x) (w x) e (f x) (c x) (g x) δ := by
   obtain ⟨c0,C0,hc,hC,H⟩:= reduces (degreeCost (G:=G) (L:=L) δ) (1/2) (by norm_num)
   let f0 x:=min 1 (c0 x); have hK x:0<f0 x:= lt_min zero_lt_one (H x|>.1); let a x:= (min (1/2) (f0 x))/16
   have ha x:0 < a x:= div_pos (lt_min (by norm_num) (hK x)) (by norm_num)
   have h₁ x:16*a x ≤1/2:= by unfold a; have h:=min_le_left (1/2:ℝ) (f0 x); linarith
   let mD x:= degreePrice (radiusB x) 1 δ; have h₂ x : mD x* (16 * a x) ≤ 1/2:= by
     apply le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (show 0 ≤ 16*(a x) by have h:= ha x; positivity))
     apply (mul_le_mul_of_nonneg_left (show 16*(a x)≤ c0 x from ?_) (abs_nonneg _)).trans (H x|>.2.2)
     unfold a
     apply le_trans _ ((min_le_right (1/2:ℝ) (f0 x)).trans (min_le_right 1 (c0 x))); linarith only
   have hΞ : Geo G L a:= by refine (Geo.fixed 1).small (Eventually.of_forall fun x=> ?_); rw [abs_of_pos (ha _),abs_one]; linarith only [h₁ x]
   have hV : Geo G L (fun x=> (a x)⁻¹):= by
     refine ((Geo.fixed 16).times ((Geo.fixed (2:ℝ)).joins hC.mean)).small (Eventually.of_forall fun x=> ?_)
     have hP:= H x|>.1
     unfold a f0; by_cases hh: c0 x < 1
     · rw [min_eq_right hh.le]; by_cases hb:c0 x ≤1/2
       · rw [min_eq_right hb,inv_div, H x|>.2.1, abs_of_pos (by positivity),abs_of_pos (by positivity), abs_of_pos (by positivity)]; rw [div_eq_mul_inv]; apply mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_two) (by norm_num)
       rw [min_eq_left (le_of_not_ge hb),abs_of_pos (by positivity),abs_of_pos (by positivity)]; nlinarith [abs_nonneg (C0 x)]
     rw [min_eq_left (le_of_not_gt hh),min_eq_left (by norm_num), abs_of_pos (by positivity),abs_of_pos (by positivity)]; nlinarith [abs_nonneg (C0 x)]
   let p := Q.rate; have ht': p<0 := Q.stop; let P' x:= Geno Q j k 1 (f x)
   have hf : Geo G L P' := by refine ((Geo.fixed (Geno Q j k 1 1)).times h).compact (Eventually.of_forall fun x=> ?_); unfold P'; simpa only [mul_one] using (gen_form Q j k (1:ℝ) (f x))
   let b:= Slides Q 1; have hb:= Geo.fixed (G:=G) (L:=L) b
   let T x:= |P' x|+|b|+(degreePrice (radiusB x) 1 Q.δ); have hX : Geo G L T:= (hf.mean.joins hb.mean).joins (degreeCost Q.δ); let T' x:=T x*(a x)⁻¹
   have h₃ x: 0 ≤ degreePrice (radiusB x) 1 Q.δ:= by unfold Trees.degreePrice Trees.stretch; have h:= Q.pos; positivity
   have h₄ x:0 ≤ T x:=by unfold T; linarith [abs_nonneg b,abs_nonneg (P' x),h₃ x]
   obtain ⟨w,V,hw,hV',hY⟩:= reduces (G:=G) (L:=L) (f':=T') (hX.times hV) 1 zero_lt_one; have hv' x : 0<w x:= hY x|>.1
   let K (x:ℝ) := (e+1)*wageIn Q L x; let A x:= K x*V x
   obtain ⟨v,U,hv,hu,hW⟩:= reduces (f':=A) (((Geo.fixed _).times (wager Q L)).times hV') (1/2) (by norm_num)
   have hZ : ∀ᶠ x in atTop, |zephyr Q L x*(g x)^j*(Q.costs L μ 1 x 0).rootHit * V x|≤1/2:= by
     have he : Rate G L (Width Q L) (zephyr Q L):= Rate.power
     refine (((he.mul (hp.pow _)).mul (Q.rate_root L hm)).mul hV'.rate).below ?_ _ (by norm_num); unfold Width; rw [zero_mul]; linarith [Q.stop]
   refine ⟨v,w,a,U,hv,hw,hΞ,hu,?_⟩; filter_upwards [hZ] with x h'; obtain ⟨hw,hfQ,hS⟩:=hY x
   have hh: T x * w x ≤ a x:= by
     have ht:T x*w x /a x ≤ 1:=by
       rw [div_eq_mul_inv,mul_right_comm]; exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self (T' x)) hw.le) hS
     exact (div_le_one (ha x)).mp ht
   obtain ⟨hu,hv,hX⟩:= hW x
   rw [hfQ, ←div_eq_mul_inv] at h'
   refine ⟨hv,⟨?_,hw,hu,?_,wage_in_pos Q L x, max_le ?_ ?_,ha x,h₁ x,?_,?_⟩⟩
   · have ht:= (div_le_iff₀ hw).1 ((le_abs_self _).trans h')
     have hz: K x *v x / w x≤1/2:=by rw [div_eq_mul_inv,mul_right_comm, ← hfQ]; exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hu.le) hX
     have hz: e*wageIn Q L x*v x+wageIn Q L x*v x≤1/2*w x:= by
        rw [← show K x * v x = e*wageIn Q L x*v x+wageIn Q L x*v x from (by unfold K; ring)]; exact (div_le_iff₀ hw).1 hz
     linarith only [ht,hz]
   · rw [chew]; refine le_trans ((mul_le_mul_of_nonneg_right ?_ hw.le).trans hh) ?_
     · exact le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))
     linarith only [h₁ x]
   · rw [slides_form]; apply le_trans (mul_le_mul_of_nonneg_right ?_ hw.le) hh
     exact (le_abs_self b).trans ((le_add_of_nonneg_left (abs_nonneg (P' x))).trans (le_add_of_nonneg_right (h₃ x)))
   · rw [gen_form,← show Geno Q j k 1 (f x)= Geno Q j k 1 1 * f x from ?_]; swap
     · simpa only [mul_one] using gen_form Q j k 1 (f x)
     refine le_trans (mul_le_mul_of_nonneg_right ?_ hw.le) hh; exact (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg b)).trans (le_add_of_nonneg_right (h₃ x)))
   · rw [chew]; have he:= h₂ x; change mD x*a x ≤ _; linarith
   rw [chew]; exact h₂ x
end spline

lemma pertinent {ι:Type}[Fintype ι] (M:ι→Leaf R)(g:ι→ℝ) (he:Bench M g d) (z:Head S) : (∀ i,0≤g i) ∧ 0 ≤ Tickets.extra (Palette.sign M S) (Palette.wages M g) z:= by
  obtain ⟨o,_,h,-⟩:=he; refine ⟨h,sum_nonneg fun i _=>?_⟩
  split; exact mul_nonneg (h _) (M i).profit; exact le_rfl
variable [Fintype ι]
variable (M:ι→Leaf R)(g:ι→ℝ)
section earn
variable {b u Dk : ℝ} (he:Bench M g b)(hp:Payment Q R s S)(h₁:1≤ zephyr Q L s)
variable {G' Y : ℝ} (hc:Coins Q L μ s j k b w e B Y r δ)(hm:0≤a)(hy:0<δ)(hz:a+δ+δ≤Q.exp)
include hp hc he h₁ hm hy hz
lemma tracks (hF : Team.Range Ω e B G' Dk k) : Resin.Ringlet H M g a δ Y (16*Y):= by
  have h:= fun i=> pertinent M g he (Palette.sign M S i)|>.1 i
  let t:=H.text; have hh:0≤H.faresP.rootHit := H.laws.acquired.γ.le -- notation
  have hY:= hF.paidE
  have ht:Bench M g b:=he
  have hr : Hired M g H w:= by
    have hx:= H.laws.acquired; let z:= Tickets.extra (Palette.sign M S) (Palette.wages M g)
    have hdZ:∀ i,0 ≤ (toll M H g) i:= fun i=>add_nonneg (H.positive _) (pertinent M g he i|>.2)
    refine ⟨hc.born,Q.pos,hc.boots,(by norm_num),fun i=>mul_nonneg (hdZ _) (Real.exp_nonneg _),fun i=>?_⟩
    let X:= Q.costs L μ 1 s 0; let w:= z
    have ht: Ac.Hit H.supportP (radiusB s) (tariff H.text (stairs H) (tolling H) Q.ε) Q.relative X.rootHit:= (Mixed.ready_vertices S _ _ _ _ _ _ _ hx H.armed).2.2.2.2.2
    have he':= additive (X:=X.rootHit) ht (ticketsExtra M g H hp he)
    apply budget_loosen (he' i)
    apply le_trans _ hc.first; have hh':0≤X.rootHit:=hh
    have hw : X.rootHit ≤ zephyr Q L s*r^j*(K₁).rootHit:= le_mul_of_one_le_left hh' (one_le_mul_of_one_le_of_one_le h₁ (one_le_pow₀ Ω.active))
    linarith only [hw,mul_nonneg (mul_nonneg hF.paidE hc.rate_r) hc.sits.le, show X.rootHit=(Q.costs L μ 1 s 0).rootHit from rfl]
  obtain ⟨hg,h'⟩:= Resin.rates M g H hr h hz hy ((le_max_left ..).trans hc.next) hc.short hc.heat
  exact ⟨h,hm,hy,hg,h',le_rfl,(by have h:=hc.short; positivity),hc.more,hc.restore⟩
-- regular b and banks
lemma enrollment (Ω:Utopia H j v d r C' χ) (h: Worthy Ω (fun _=>1) D') (U:Knot Ω e B u Dk A G' k) (hx:1≤ Height.grow G L s)
    (hv: (Tithe.portion R.activities Ψ).EBound R.p κ) (hs: κ ≤ 1) (ht:1≤D') (hw:1≤D) (hT: D * κ ≤ b) (n:ℕ): ∃ x:ℕ→ℝ, Casing R x Ψ ∧
    Ac.Hit (origins M H) (radiusB s) (fun p=> Baked.weight M (fun v=> sheen M v Ψ D (zephyr Q L s) D') p*RegDebt M g p Ω k n B (maskRaise Ω Ψ x e)) a
    (collars G δ s j n * (Y*(1-1/2:ℝ)⁻¹)) := by
  obtain ⟨x,hx',hZ⟩:= portion_sale hp hv H hs
  let v:= liftedPay Ω Ψ x e D (zephyr Q L s) D'; have hp':∀ i,0≤v i:= pay_ge Ω hw h₁ ht hx' U.paidE
  let z:= Tickets.extra (Palette.sign M S) (Palette.wages M g)
  have hrA i:= (pertinent M g he (Palette.sign M S i)).1 i
  have hB:= crownPay Ω h hx hw h₁ ht hx' U.paidE hZ
  have hr : Ready H.supportP (radiusB s) (tariff (fun i=> v i+z i) (stairs H) (tolling H) Q.ε) (Q.exp+2*Q.ε) w Q.δ (1/2):=
    ⟨hc.born,Q.pos,hc.boots,by norm_num,fun i=>mul_nonneg (add_nonneg (hp' i) (pertinent M g he i|>.2)) (Real.exp_nonneg _),fun i=>budget_loosen (additive (v:=Q.relative) hB (ticketsExtra M g H hp he) i) (by
        refine le_trans ?_ hc.first; rw [mul_comm b]; refine add_le_add (add_le_add le_rfl ?_) le_rfl; refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hT (mul_nonneg U.paidE hc.rate_r)); ring
        )⟩ -- order
  have hu:= Baked.roll M g Ω hw h₁ ht hx' U.paidE U.paidB hrA hr k hm hy hz ((le_max_right ..).trans hc.next) hc.short hc.heat
  exact ⟨x,hx',Pillow.brocade M g U hx' hrA hm hy (fun i=> zero_le_one.trans (sheen_paid M i hw h₁ ht)) hu⟩
end earn
end Foreman
end YM.RGComparison01.Pledge
