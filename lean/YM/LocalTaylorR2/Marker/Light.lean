import YM.LocalTaylorR2.Marker.Favorite
import YM.LocalTaylorR2.Curriculum
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
structure Tinted (G:Gauge)(b r d W:ℝ)(L:Side)(χ:Chi)(j:ℕ) : Prop where
  salt : 0≤r
  motion : ∀ (c f:Side) (S:StepData c f) (T: Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=b → X.χ=χ → S.patch.L=L → 0 < 2*W*X.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (z : Air f G) (a β : ℝ) (y:E) (U : E→ Config G c) (f':E → Directions G f) (w:E → Air f G), Clutch X z a β d y j U f' w →
        ∀ Y (M:Support c),Y⊆ M → Brush j 1 (r*coverNumber X.B M) (fun y=> X.enforce (2*W) (f' y) (X.plaza Y)) y

variable {j l k n:ℕ} {D K e v₀ d r θ ζ y b bm q A :ℝ} {χ:Chi} {Ξ:Utopia H j v₀ d e q χ}
variable (B:LocalBookingsR2 ζ bm Ξ) (ht: Tinted G x r d o.a L χ j)
lemma tinted (V: ℝ→ℝ) (h:Rate G L (-(1/2)) V) (b:ℝ) : ∃ r:ℝ→ℝ, Rate G L 0 r ∧ ∀ᶠ s in atTop,Tinted G s (r s) (V s) b L χ j := by
    obtain ⟨C,hC,hv,H⟩:= Silica.Clutch.central G L χ j h (2*b); exact ⟨C,hC,H.mono fun x hx=>⟨hv x,hx⟩⟩

include ht H
lemma bearing (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (F:Forest S.ratio) (X:Coat T F)
      (V:E→ Config G c) (u:E→ Directions G f) (z:E→ Air f G) (a:E) (w:Air f G) (hx:X.x=x)(hp:X.χ=χ)(hh : Clutch X w o.a R.beta d a j V u z) : Brush j M.weight (r*spanW T R X.B Q.halo (i₀)) (fun y=> M.fond (vary X (V y)) o.a (u y) (X.input (worldZ X R.beta w))) a:= by
    have he : areas R T 0 X.B (i₀) ⊆ H.supportP (i₀) :=by
      change _⊆ areas R T Q.halo (radiusB x) (i₀); simp_rw [M.turn.badge_area]; exact Corona.halo_mono (by simp) (Subset.refl _)
    have hy : 0<(2*o.a)*X.t:= by have hv:= hh.pulse; rw [mul_assoc]; positivity
    have hM := ht.motion c f S T F X hx hp H.laws.data.funds.length_eq hy E w o.a R.beta a V _ _ hh _ _ he
    have hV := (Brush.certified (d:=0) (x:=a) (k:=j) le_rfl (M.ingredient (X.input (worldZ X R.beta w))) |>.climb (M.earn _) le_rfl).paints hM
    rw [mul_one, zero_add] at hV; apply hV.climb le_rfl
    apply mul_le_mul_of_nonneg_left _ ht.salt; rw [← sparkPath]
    change (coverNumber X.B (footprints T R _ (radiusB x) _):ℝ) ≤ 1+(_ + _)
    rw [← show X.B=radiusB x from congr_arg radiusB hx]
    apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact le_add_of_nonneg_right (Nat.cast_nonneg _)

lemma markedSees : Sees H j v₀ d χ (stems M H) M.weight (r*spanW T R (radiusB x) Q.halo (i₀)) :=by
    intro E _ _ _ F X V u z x₀ w hx hK hM hχ hv hf
    rw [← show X.B=radiusB x from congr_arg radiusB hx]; apply Brush.shimmy (bearing M H ht _ F X V u z _ _ hx hχ hf)
    filter_upwards [hf.patch] with y hy
    let Z:=vary X (V y); change M.paidU Z o.a _=_; rw [hf.moving y]; unfold Leaf.paidU; exact M.canv Z _ _ _ (plastic hy hf.pulse)

abbrev speedS (r e:ℝ) (l:ℕ):ℝ:= 2*r+2*e*(l+3:ℝ)
include B
lemma team_sees {p:H.ThinP} (q:Paint (partners M p.val) l) (hp:treads M H p) (ha:Allows l j θ) (hv:∀ i,Ξ.goalsL i≤1): Sees H j v₀ d χ (team M H (p:=p) q) (M.weight*Tender.forge Ξ θ q) (speedS r e l*(1+H.shapeW p.val)):=by
  refine Sees.climb H (Sees.times H (markedSees M H ht) (Charge.sumSpeed B q (Finset.erase_subset ..) hp.1.2 ha hv)) le_rfl ?_
  let f i:= spanW T R (radiusB x) Q.halo i
  have he : f (i₀) ≤ 2*H.shapeW p.val:= (Finset.single_le_sum (s:=p.val) (fun i _=> show 0≤f i from ?_) hp.2).trans (Utopia.worthy _ hp.1.2)
  · nlinarith only [mul_le_mul_of_nonneg_left he ht.salt,ht.salt]
  rcases i with i|i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
omit B
include ht
lemma herded (U:StoresR2 H j v₀ d A D k y n χ) (hw:y*(1+D+2*(e+r))^j ≤ K) : Herd H Ξ A K (n+j):= by
  refine ⟨⟨?_⟩,?_⟩
  · intro E _ _ _ F X Y y₀ p hζ hη hX hK hr hu he hf hy' m'
    obtain ⟨f,hF,h1,h2⟩:= (U.earnings Ξ).tents E F X Y y₀ p hζ hη hX hK hr hu he hf hy'
    have hh : 0≤ Ξ.meant p (n+j):= by
      unfold Utopia.meant; rw [if_pos ((H.attends p).2 he)]
      exact mul_nonneg (prod_nonneg fun _ _=> Ξ.fares _) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _)
    refine ⟨f,hF,h1.trans (mul_le_mul_of_nonneg_right (le_trans (b:= y*(1+D+2*(e+r))^j) ?_ hw) hh),h2⟩ -- comp
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans U.sure); apply pow_le_pow_left₀ (by have h:= U.fuel; have hp:=Ξ.active; positivity) _ ; linarith only [ht.salt]
  intro M E _ _ _ F' X Y y' p' hζ hM hx hK hr hu he ha hf hy m'
  let I:= edgesM S (H.unionP p') (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p'); let U' := p'.erase (M.turn.badge S) -- literal M binder.not i₀
  let f(z : Air f G):= facescale I z^(k*j); let S':=1+H.shapeW p'; let X' z:= J.indicator f z
  let a:=(M.weight*∏ i∈U', Ξ.tag i)*(1+D+2*(e+r))^j*S'^j
  have hD:=U.fuel
  have hx':(1:ℝ)≤S':=le_add_of_nonneg_right (H.positive_volume _)
  have hb : 0≤a:= by unfold a; have ha:= mul_nonneg M.profit (prod_nonneg (show ∀ i∈U',0≤ Ξ.tag i from fun _ _=>Ξ.tagged _)); have h0:= ht.salt; have h:=Ξ.active; positivity
  obtain ⟨hV,hA⟩:= U.curtain p' F' X hx hζ hK hM a hb (Ξ.rad^(blaze p').card) (pow_nonneg Ξ.awake _) J (Poll.sounded ..)
      (by rw [← pow_mul,Nat.mul_comm,pow_mul]; exact Ξ.ship _ X hx hK hζ hM (blaze p'))
  refine ⟨fun z=> a*X' z.2,hV,le_trans hA ?_,?_⟩
  · apply le_trans _ (mul_le_mul_of_nonneg_right hw (mul_nonneg (dew M H|>.2.1) (earned M H q Ξ.flair Ξ.fares ..)))
    apply le_of_eq; unfold a U' S'; rw [photo M H Ξ (n+j) he ha]; ring
  intro ⟨v',z⟩; let W:= X.wrapY v'
  obtain ⟨hp,hq⟩:= U.flight F' W hx hζ hK hM z E Y y' hy hf
  apply (Daisy.score (z':=z) M W H Ξ hu ha hx hK hζ (show W.manifest from hM) hr hf hp ht.salt (bearing M H ht _ F' W Y _ _ _ _ hx hζ hp) (hq p') hD).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤ a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
end YM.LocalTaylorR2.Marker
