import YM.LocalTaylorR2.Canvas.Origins
import YM.LocalTaylorR2.Mesh.Pigment
/-!
 # Simultaneous argument Taylor substitution on rootface itself. Before
 touching the mean or measure. On all physical costs, uses LOG of principal
 in the same chart representation & angular jets on EVERY required local background.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Canvas
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R:Rep G f}{X X':Coat T F}{b a γ W α y' ζ d q :ℝ}{χ:Chi}{j p' l :ℕ}
open Work.G05 Animals Itinerary

def bed (X : Coat T F) := 7*X.B/8
def arbor (J:Basecamp G)(X : Coat T F)(i : Stream c f) (u : Directions G f) : ZipP G c f:= let o:= lead S i.2; let z:= i.1; let V := pull z 0 X.V
    (point J X.χ (bed X) o V, fun p=> if distAt S p o≤bed X then spinRow S (carrier o V) (displacement z (X.signal u) (replica S.ratio X.V)) p else 0)

def rootTaylor (J: Basecamp G)(X:Coat T F) (i:Stream c f)(p:ℕ)(u:Directions G f):= blockTaylor p (ivy T X.x (choice i.1 X.k) i.2) (arbor J X i u)
def pineCone (J:Basecamp G)(X : Coat T F) (A : ℝ) (R : Rep G f) (i: Stream c f) (p:ℕ) (u:Directions G f):= let o:=rowSite S i
    if Inside o X.seeds (200*X.B) then 0 else -R.beta*Raw.orientation*(X.enforce (2*A) u (X.booth o)*rootTaylor J X i p u+Vine.costs X (voltage X) i.1 i.2)
lemma preserver (J: Basecamp G) (P:Teller G) (L : Side) (j : ℕ) (χ:Chi)(a:ℝ) {V u : ℝ→ℝ}(hv:Rate G L (-(1/2)) V)(ht:Rate G L (-(1/2)) u)(he:∀ᶠ x in atTop,0≤V x): ∃ b:ℝ→ℝ, Rate G L (-(1/2)) b ∧ ∀ᶠ s in atTop,0<b s ∧ ∀(c f:Side)(S:StepData c f)(T:Tube G S)(F:Forest S.ratio)(X:Coat T F), S.patch.L=L → X.x=s → Room P S T X.x → X.manifest → X.χ=χ → ∀(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (V':E→ Config G c)(U:E→ Directions G f)(W:E→Air f G)(w:Air f G)(y:E)(β:ℝ), Mode V' y j (V s) → Clutch X w a β (u s) y j V' U W → ∀ i:Stream c f, ¬ Inside (rowSite S i) X.seeds (200*X.B) →
    (¬ (fun x=> X.enforce (2*a) (U x) (X.booth (rowSite S i)))=ᶠ[𝓝 y] fun _=>0) →
    let q x:= vary X (V' x); let t x:=arbor J (q x) i (U x)
    Brush j (b s) 1 t y ∧ ∀ᶠ x in 𝓝 y, Polar.rootface (q x) (U x) (X.input (worldZ X β w)) true i.1 i.2=ivy T X.x (choice i.1 X.k) i.2 (t x) :=by
  obtain ⟨C,hC,hY⟩:= Basecamp.tenant G L P J j hv he
  let B x:= radiusB x; let g:= royalty G; let Z x:=4*(B x:ℝ)*(V x*g); let p x:=u x+4*a*Pressure.fiery G x L
  let f x:= g*(p x*g)*(1+(V x +1+ V x))^j; let Y x:= (g*(f x*g))*(1+(Z x+1+Z x))^j
  have hZ : Rate G L 0 Z := by simpa only [zero_add] using! ((Rate.radius_price.mul_left 4).mul ((hv.mul_right g).weaken (b:=0) (by norm_num)))
  have hy (e) (h:Rate G L 0 e): Rate G L 0 (fun x=> (1+(e x+1+e x))^j) := by simpa only [zero_mul] using! (((Rate.const 1).add ((h.add (Rate.const 1)).add h)).pow j)
  have hF:Rate G L (-(1/2)) f := by simpa only [add_zero] using! ((((ht.add (Rate.flame.mul_left (4*a))).mul_right g).mul_left g).mul (hy V (hv.weaken (by norm_num))))
  have hΩ:Rate G L (-(1/2)) Y := by simpa only [add_zero] using! (((hF.mul_right g).mul_left g).mul (hy Z hZ))
  let K x:= C x+|Y x|; have hp':Rate G L (-(1/2)) K := hC.add (hΩ.compare (Eventually.of_forall fun x=>(abs_abs _).le))
  refine ⟨fun x=> K x+K x,hp'.add hp',?_⟩; filter_upwards [hY] with s hE; have hp : C s ≤ K s:=le_add_of_nonneg_right (abs_nonneg _); have hh:= hE.1.trans_le hp
  refine ⟨add_pos hh hh, ?_⟩
  intro c f S T F X hL hX hP hΛ hχ E _ _ V' U W w y β hm hu i hx hν q t; subst s χ
  obtain ⟨-,hq,hH,hy⟩:= hu.torchR2 hP hm hΛ i hx hν; dsimp only at hq hy hH
  let d:=bed X; let o:= lead S i.2; let U' x:= pull i.1 0 (V' x); let A x:=displacement i.1 ((q x).signal (U x)) (replica S.ratio (V' x))
  have hx' : Clean (U' y) X.x o (40*X.B+1):=by
    unfold U'; rw [hu.atV]; exact ((clean_far X.seeds X.V hΛ hx).shrink (v:=rowSite S i) (D:=40*X.B+1)
      (by rw [separation_self]; have hx:100≤X.B:=hP.sight.1; omega)).turn
  have hU: Mode U' y j (V X.x):= Blaze.turn hm i.1
  obtain ⟨hz,hτ⟩:= hE.2 _ _ S T hL hP d (by unfold d bed Coat.B; omega) E U' y X.χ o hU hx'
  constructor
  · suffices hv:Brush j (K X.x) 1 (fun x=> (t x).2) y from Brush.pair (hz.climb hp le_rfl) hv
    refine Brush.fold zero_le_one hh.le (fun i'=> ?_); by_cases hi : distAt S i' o≤d; swap; exact Brush.zi (Eventually.of_forall (fun i' => if_neg hi)) hh.le zero_le_one
    have ha:= hq i' hi; unfold Coat.t at ha; rw [hL] at ha
    let z x:= carrier o (U' x) (atEdge S i'); have hv: Brush j g (Z X.x) (G.mat ∘ z) y:=by
      apply (tour (carriage o (atEdge S i')) o (hU.pos) hU.atLink).climb le_rfl
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hm.pos (zero_le_one.trans (royalty_ge _)))
      exact_mod_cast (SliceRows.mileage o _).trans (Nat.mul_le_mul_left 4 (hi.trans (by unfold d bed B Coat.B; omega)))
    apply (((decorate hv ha).trim).climb ( (le_abs_self _).trans (le_add_of_nonneg_left (show 0≤C X.x from hE.1.le))) le_rfl).shimmy
      (Eventually.of_forall fun i'=> if_pos hi)
  filter_upwards [hτ,hH] with x hv hu
  rw [show rootface _ _ _ true _ _= _ from hy x]
  apply placementR2 hP i.2 (choice i.1 X.k) (carrier o (U' x)) (t x) (A x) d le_rfl hv hu; intro p hp; exact Eq.symm (if_pos hp)

lemma ordinance (G:Gauge)(L:Side)(J:Basecamp G)(P:Teller G)(v d:ℝ→ℝ) (hv:Rate G L (-(1/2)) v)(hd:Rate G L (-(1/2)) d)(hh:∀ᶠ x in atTop,0≤v x) (χ:Chi) (p j:ℕ) (W:ℝ)(o: Target.Order G W) (D:Patch)(hD:D.Branches P.bind G): ∃ K : ℝ→ℝ, Rate G L (-(p+1)/2) K ∧ ∀ᶠ s in atTop, ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(R:Rep G f)(μ C :ℝ)(Q:YM.ConnectedActivityE6.Target G P)(H: Cash W s μ L Q o C T R), S.patch=D → ∀ i:Stream c f, Sees H j (v s) (d s) χ (fun F X w=> Port.weightLog H (.inr (.inl (.inl i))) F X w- pineCone J X o.a R i (p+2) (worldZ X R.beta w)) (|K s|) 1:=by
  obtain ⟨s,hS,h⟩ := preserver J P L j χ o.a hv hd hh; obtain ⟨B,hB,hP,hY⟩:= Clutch.central G L χ j hd (2*o.a); obtain ⟨r,hr,hr',M,hM,hF⟩:=growth P L D hD (j+(p+2)+1)
  let u x:= (1+(81*B x+1))^j; let A x:= ((j.factorial*M x)*((1+((1+1)*1):ℝ))^j*s x^(p+2+1))*u x
  refine ⟨fun x=> (2*betaF G x L)*A x,?_,?_⟩
  · have hP':Rate G L 0 u:=by simpa only [zero_mul] using! (((Rate.const 1).add ((hB.mul_left 81).add (Rate.const 1))).pow j)
    convert ((Rate.hat.mul_left 2).mul ((( (hM.mul_left _).mul_right _).mul (hS.pow (p+2+1))).mul hP')) using 1; push_cast; ring
  filter_upwards [h,hF,hY,hS.below (by norm_num) r hr] with x h hM hp ht c f S T R μ C Q H hS' i E _ _ _ F X V g z y w he hw hΛ hχ hV hu
  let p' t:= X.enforce (2*o.a) (g t) (X.booth (rowSite S i)); let Y t:= vary X (V t)
  have hx : Intake P T X.x R:= he.symm ▸ H.laws.intake; have hT : Room P S T X.x:= he.symm ▸ H.laws.data.room; have hL:= H.laws.data.funds.length_eq
  let K t:= rootTaylor J (Y t) i (p+2) (g t)
  let U t:= rootface (Y t) (g t) (X.input (worldZ X R.beta w)) true i.1 i.2
  let a t:=arbor J (Y t) i (g t)
  by_cases hμ : Inside (rowSite S i) X.seeds (200*X.B); · exact Brush.zi (Eventually.of_forall fun t=> by change (hover _ _ _ _ _ _) - pineCone ..= (0:ℝ); unfold hover pineCone; change (if Inside _ X.seeds (200*X.B) then 0 else _) -(if Inside _ X.seeds (200*X.B) then 0 else _)= _; simp only [if_pos hμ,sub_self]) (abs_nonneg _) zero_le_one
  have hq:(fun t=>Port.weightLog H (.inr (.inl (.inl i))) F (Y t) (z t) - pineCone J (Y t) o.a R i (p+2) (worldZ (Y t) R.beta (z t))) =ᶠ[𝓝 y] (fun t=> (-R.beta*Raw.orientation)*(p' t*(U t-K t))) :=by
    filter_upwards [hu.patch] with t ht
    have hX:= (plastic ht hu.pulse).reeled hT W Q.table ∅ Q.halo hx (Port.identityLog (S:=S) (.inr (.inl (.inl i)))) (z t)
    have hz : Port.weightLog H (.inr (.inl (.inl i))) F (Y t) (z t)=hover (Y t) o.a R (g t) (X.input (worldZ X R.beta w)) i:= by
      unfold Port.weightLog; rw [show worldZ (Y t) _ _= g t from hu.moving t]; exact Real.exp_injective (sub_left_inj.mp (show Real.exp _-1=Real.exp _-1 from hX))
    rw [hz,show worldZ (Y t) _ _=g t from hu.moving t,hover,pineCone]; rw [if_neg (show ¬Inside _ (Y t).seeds (200*(Y t).B) from hμ),if_neg (show ¬Inside _ (Y t).seeds (200*(Y t).B) from hμ)]; unfold U K; change _*(p' t*_+_)- _*(p' t * _ + _)=_; ring
  by_cases hh:p'=ᶠ[𝓝 y] fun _=>0; · exact Brush.zi (hq.trans (hh.mono fun i hi=> by change _*(p' i*_)=(0:ℝ); rw [show p' i=0 from hi,zero_mul,mul_zero])) (abs_nonneg _) zero_le_one
  obtain ⟨hS,hK⟩:= h.2 _ _ S T F X hL he hT hΛ hχ E V g z w y R.beta hV hu i hμ hh
  let L' := ivy T X.x (choice i.1 X.k) i.2
  have hf : Brush j ((j.factorial*M x)*((1+((1+1)*1):ℝ))^j*s x^(p+2+1)) 1 (fun t=> U t-K t) y:=
    (Mesh.priced h.1 (( (le_abs_self _).trans ht).trans hr') (f:=L') (fun u hu=>  (show Brush (j+(p+2)+1) (M x) 1 (ivy T X.x (choice i.1 X.k) i.2) u from by rw [he]; exact hM _ _ S T hS' hL (he ▸ hT) _ _ _ (hu.trans ((le_abs_self _).trans ht)))) hS).shimmy (hK.mono fun x hx=> congr_arg₂ (·-·) hx rfl)
  let m:= Animals.neighbors X.B (rowSite S i)
  have he': 0<2*o.a*X.t := mul_pos (by have h:=o.large; positivity) hT.fiery
  have hb := hp c f S T F X he hχ hL he' E w o.a R.beta y V g z hu m m (Subset.refl _)
  have hB: Brush j 1 (81*B x) p' y:= hb.climb le_rfl (by
    rw [mul_comm (81:ℝ)]; apply mul_le_mul_of_nonneg_left _ (hP _)
    have hx' := Lattice.Corona.tile (rowSite S i) 1 X.B (show 0<X.B from lt_of_lt_of_le (by norm_num) hT.sight.1)
    rw [Nat.one_mul] at hx'; exact_mod_cast hx')
  have hv :Brush j (A x) 1 (fun t=> p' t*(U t-K t)) y:=by simpa only [one_mul] using! (hB.paints hf).trim
  subst x
  refine ((hv.smul (-R.beta*Raw.orientation)).climb ?_ le_rfl).shimmy hq
  rw [norm_mul,norm_neg,Real.norm_of_nonneg hx.positive.le,Real.norm_of_nonneg Raw.orientation_range.1.le]; apply ((mul_le_mul_of_nonneg_right _ hv.nonneg)).trans (le_abs_self _)
  exact ((mul_le_of_le_one_right hx.positive.le Raw.orientation_range.2).trans (show R.beta≤ _ from (by rw [← hL]; exact hx.window.2)))
end YM.LocalTaylorR2.Canvas
