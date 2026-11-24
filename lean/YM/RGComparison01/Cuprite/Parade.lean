import YM.RGComparison01.Cuprite.Role
import YM.RGComparison01.Loads

/-!
# Full unmarked variant, clock finance

 Big band same for all index, allow roofs up to aux.side. Choose Ward upright.
 Budget criterion absorbs ζ. Keep `R.variants` unchanged.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Cuprite
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Push.AbsoluteSums.Animals Slide Tensor WilsonStartup Bouquet Push.PriceCompiler
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves
open RG.Supply Shoot Input Org Ovens Progress.DirectedRecipe Next.Scheduling Further.PhysicalPeriodLimitF933
open Vision Ward
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {L : Side} {P : Teller G} {K : KernelChoices} {C Z W' μ σ Λ σ' C' T₀ : ℝ} {q q' n k b p j j': ℕ} {v d W u y : ℝ→ℝ}
variable (D:Duplex G k)(b:ℕ)
local notation "R"=> (royalty G)
local notation "Y"=>fun t:ℝ=>Trio.fence b (radiusB t)
lemma prim (i:Stars): Geo G L (fun t=>D.C.wing (Y t i) D.rate) ∧ Geo G L (fun t=>Visage.berth G (Y t i) k D.rate) ∧ Geo G L (fun t=> D.conjCost j (Y t i)):= by -- Y macro parentheses?
  let M (x:ℝ):= Trio.fence b (radiusB x) i
  have hv : Geo G L (fun x=> ((M x).val:ℝ)):= by
    change Geo G L (fun x=> (↑(2*(Trio.tent b (radiusB x)+i.val)) : ℝ)); simp only [Nat.cast_mul (α:=ℝ) 2, Nat.cast_add («R»:=ℝ) (Trio.tent b _), Nat.cast_ofNat]; exact (Geo.fixed 2).times ((Geo.basic (Trio.rows G L b).2.1).joins (Geo.fixed _))
  have he : Geo G L (fun x=> longitude D.rate (M x).val (royalty G)) := ((((Geo.fixed 4).times hv).times (Geo.fixed _)).times (Geo.fixed _)).joins ((Geo.fixed _).joins (((Geo.fixed 4).times hv).times (Geo.fixed _)))
  have hP : Geo G L (fun t=>D.C.wing (M t) D.rate):= (Geo.fixed _).times (((Geo.fixed 1).joins ((Geo.fixed _).times he)).power k)
  exact ⟨hP,(Geo.fixed _).times (((Geo.fixed 1).joins he).power _),((((Geo.fixed 1).joins hP).power _).times (Geo.fixed _))⟩
lemma prior (a:ℝ→ℝ)(ha:Geo G L a): ∃ v : ℝ→ℝ,Geo G L v ∧ ∀ᶠ x in atTop, ∀ i:Stars,∀ β, Pressure.betaF G x L/2 ≤ β → 0<β → 1<a x → furl G L x < a x*gStep β →
    1 < v x ∧ v x*gStep β ≤ 1 ∧ D.Blurb (Trio.fence b (radiusB x) i) (a x*gStep β) (v x*gStep β) (furl G L x):= by
   let W (i:Stars)(x:ℝ):= D.C.wing (Y x i) D.rate
   let C x:= ∑ i:Stars,|W i x|; let t x:=(C x+2)*a x
   have hv: Geo G L C:= Geo.expel Finset.univ (fun i x=> |W i x|) (fun i _=> (prim (j:=0) D b i).1.mean)
   have ht : Geo G L t:= (hv.joins (Geo.fixed 2)).times ha
   refine ⟨t,ht, eventually_all.mpr fun i=>?_⟩
   filter_upwards [ht.uniform zero_lt_one, ((prim (j:=0) D b i).2.1.times ha).uniform D.C.charged] with x hx he β h hi hh hd
   have hb:= Fare.gS β hi|>.1; have hp:0<a x*gStep β:=mul_pos (zero_lt_one.trans hh) hb
   have hC:0 ≤ C x:= Finset.sum_nonneg fun _ _=> abs_nonneg _
   have he':a x ≤ t x:= le_mul_of_one_le_left (zero_lt_one.trans hh|>.le) (by linarith only [hC])
   refine ⟨lt_of_lt_of_le hh he',((mul_le_mul_of_nonneg_right (le_abs_self _) hb.le).trans_lt (hx β h)).le,mul_le_mul_of_nonneg_right he' hb.le,hp.le,?_,?_⟩
   · rw [←mul_assoc]; exact (mul_le_mul_of_nonneg_right (le_abs_self _) hb.le).trans (he β h|>.le)
   change W i x*(a x*gStep β)+_ < (C x+2)*a x*gStep β; rw [mul_assoc (C x+2),add_mul]
   have hW:= mul_le_mul_of_nonneg_right ((le_abs_self (W i x)).trans (Finset.single_le_sum (s:=Finset.univ) (f:=fun i=> |W i x|) (fun i _=> abs_nonneg _) (Finset.mem_univ i))) hp.le
   linarith only [show W i x*(a x*gStep β) ≤ C x*(a x*gStep β) from hW,hp,hd]

section cents
variable {Q : ConnectedActivityE6.Target G P} {o: Target.Order G W'} {J:Patch} {C₀ r t:ℝ}
    {A:Before G σ C J.J K (p+3)} {c c': Clip} {u e U H Y' : ℝ→ℝ}
lemma liftH (h: H t ≤ Y' t) (he:Kraal.Launch (σ':=σ') (C':=C') (d:=d) Q o J A c c' μ j q n k u e C₀ r U H t) : Kraal.Launch (σ':=σ') (C':=C') (d:=d) Q o J A c c' μ j q n k u e C₀ r U Y' t:=by
   intro a b S X F hh hK hf hX hh' hp Λ hF ρ hρ hC i Z hx h' hw B B' m' β hT ht hv hQ v hp' D' r' hy E₀ e₀ hP hR
   obtain ⟨ha,hI,hH,hG,hE⟩:= he a b S X F hh hK hf hX hh' hp Λ hF ρ hρ hC i Z hx h' hw B B' m' β hT ht hv hQ v hp' hy E₀ e₀ hP hR
   exact ⟨ha,hI,hH,hG,hE.funding h (by unfold gStep; positivity) le_rfl⟩
end cents

variable (b k q n j : ℕ) (L: Side) (S : RG.Stage) (A : ℝ)
-- charge formula AuxWarp supplied on Big Canvas.A.Function j order.
variable (Ψ : ℝ→ℝ) (P : BareRates.pre G S.width S.paths k)(ε : ℝ→ℝ) (g:ℝ →ℝ)
local notation "U'"=> Trio.tilt
abbrev bill (x:ℝ):= |2*g x+ Bonus.baseFee P S.clip (Trio.paySide G L b x:ℝ) (ConnectedActivityE6.loopBill G L x) A (Ψ x) n| -- after Tue
abbrev niche (b k n q :ℕ)(L:Side)(S:Stage)(A:ℝ)(D: Duplex G (S.order+1))(P:BareRates.pre G S.width S.paths k) (r g : ℝ→ℝ)(x:ℝ)(i:Stars):= |2*D.conjCost S.order (Trio.fence b (radiusB x) i)* Cuprite.prom n (Pencils.bounder n q) (Cuprite.bill b k n L S A r P g x) ((r x)^2)|
abbrev headBudget (b k n q :ℕ)(L:Side)(S:Stage)(A:ℝ)(D:Duplex G (S.order+1))(P:BareRates.pre G S.width S.paths k)(r g:ℝ→ℝ)(x:ℝ):= Trio.oroW (Loads.size S (Trio.base b (radiusB x))) (Trio.base b (radiusB x)) (fun i=> Boulevard.ticket S.order (niche b k n q L S A D P r g x i))
variable (U:Duplex G (S.order+1))(hr: Geo G L Ψ)(hg:Geo G L g)
include hr hg
lemma fare : Geo G L (fun x=> Cuprite.bill b k n L S A Ψ P g x):= Geo.mean ((Geo.fixed 2|>.times hg).joins (Kraal.dangerous P S.clip n A (Trio.circles ..) hr))
lemma awesome (i:Stars): Geo G L (fun x=> Cuprite.niche b k n q L S A U P Ψ g x i):= by
   have h':= Cuprite.fare b k n L S A Ψ P g hr hg
   have hp:Geo G L (fun x=>prom n (Pencils.bounder n q) (bill b k n L S A Ψ P g x) ((Ψ x)^2)):= (Geo.fixed _).times (h'.mean.joins ((Geo.fixed _).times (Geo.mean (hr.power 2))))
   exact Geo.mean (((Geo.fixed 2).times (prim (j:=S.order) U b i).2.2).times hp)
lemma charged : Geo G L (Cuprite.headBudget b k n q L S A U P Ψ g):= by
   let f t:= Trio.base b (radiusB t)
   let C i t:= Boulevard.ticket S.order (Cuprite.niche b k n q L S A U P Ψ g t i)
   have hC i:Geo G L (C i):= (((Geo.fixed _).times (Cuprite.awesome b k q n L S A Ψ P g U hr hg i)).times (Geo.fixed ((1+(1+1))^(S.order):ℝ))) -- b & q order edit
   exact Geo.expel Finset.univ (fun i t=>|Slide.ray i| * (Trio.tilt (Loads.size S (f t)) (f t)*C i t)) (fun i _=> (Geo.fixed _).times ((Loads.tiltage b L S G).times (hC i)))

-- stipend.rise preserves all earlier interviews + cover needs
variable (u : ℝ→ℝ)(hu:Geo G L u) (Y' : Kraal.Floor G L) (d : ℝ→ℝ) (w : ℕ)
include hr hg hu
lemma remit (he:Geo G L d): ∃ p:ℝ→ℝ,Geo G L p ∧ (∀ x, u x ≤ p x) ∧ ∀ i x,
    2*U.conjCost S.order (Trio.fence b (radiusB x) i) * Cuprite.bill b k n L S A Ψ P g x ≤ Loads.rateP b n w q L S Y' P d p A x:= by
   let C t := Bonus.baseFee P S.clip (Trio.paySide G L b t:ℝ) (ConnectedActivityE6.loopBill G L t) A (d t) n + ritual_fee w n (Y'.s t) 0 (d t) + Loads.quota n q w * Y'.u t
   let f i t:= 2*U.conjCost S.order (Trio.fence b (radiusB t) i)* Cuprite.bill b k n L S A Ψ P g t
   have hC : Geo G L C:= ((Kraal.dangerous P _ _ A (Trio.circles ..) he).joins (Kraal.for_ritual w n he Y'.wings)).joins ((Geo.fixed _).times Y'.spans)
   let W t:= ∑ i:Stars,|f i t|; have hW: Geo G L W:= Geo.expel univ (fun i t=> |f i t|) (fun i _=> ((((Geo.fixed _).times (prim (j:=S.order) U b i).2.2).times (Cuprite.fare b k n L S A Ψ P g hr hg))).mean)
   let p x:= |u x|+|C x| + W x; have hv x: 0 ≤ W x:= Finset.sum_nonneg fun i _=> abs_nonneg _
   refine ⟨p,(hu.mean.joins hC.mean).joins hW,fun x=> (le_abs_self _).trans (by unfold p; linarith only [abs_nonneg (C x), hv x]), fun i x=>?_⟩
   have hX i : f i x ≤ W x:= (le_abs_self _).trans (Finset.single_le_sum (s:=Finset.univ) (fun (v:Stars) _=> abs_nonneg (f v x)) (Finset.mem_univ i))
   unfold Loads.rateP; apply le_trans _ (le_abs_self _); rw [add_assoc (2*p x),add_assoc (2*p x)]; change f i x ≤ 2*p x+C x; unfold p; linarith only [hX i,abs_nonneg (u x),abs_nonneg (C x),hv x,neg_le_abs (C x)]
end YM.RGComparison01.Cuprite
