import YM.LocalTaylorR2.Pavilion.Pinnacle
/-!
 # Attach schedule and in full rolls. Purchases on vacuum unfiltered coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Pavilion
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {D : ℕ} {o0 : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R: Rep G f}{X X':Coat T F}{J:Canvas.Basecamp G}{b a γ W α y' ζ d v q μ u C :ℝ}{χ:Chi}{j i' l :ℕ}
variable {Q:YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}{H : Cash W s μ L Q o C T R}
open Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census
section
variable {A E: Type} [NormedAddCommGroup E][NormedSpace ℝ E] {Y : A→ F.Slice G} {U:E→ Config G c}{x:E}
lemma titrates (J: Basecamp G)(X:Coat T F)(o:Site c)(h:Mode U x j v) : Zest (fun t u=> Pavilion.pitch J (drive X (U u) (Y t)) o) x j:=by
  let g u:= Canvas.point J X.χ (24*X.B) o (U u)
  refine Zest.pair (Zest.single (f:=g) (contDiffAt_pi.mpr ?_)) (Zest.still _)
  intro k; unfold g Canvas.point; split_ifs with hx
  · exact J.smooth (beacon _ _ k (separation o k.1+1) le_rfl h).smooth
  exact contDiffAt_const
end
lemma fiction (J:Basecamp G)(X:Coat T F)(o:Site c){E:Type}[MeasurableSpace E] {Y : E→ F.Slice G}{U:E→ Config G c}(h:Measurable U): Measurable (fun t=> Pavilion.pitch J (drive X (U t) (Y t)) o):=by
  have hh z:Measurable (fun t=>carrier o (U t) z):=(continuous_travel (G:=G) (carriage o z) o).measurable.comp h
  refine Measurable.prodMk ?_ (measurable_const (a:=(0:Directions G f)))
  refine measurable_pi_lambda _ (fun i=>?_); change Measurable fun y=>Canvas.point J X.χ (24*X.B) o (U y) i; unfold Canvas.point; split_ifs
  · exact (J.log.borel X.χ).comp (((hh _).mul ((measurable_pi_apply i).comp h)).mul (hh _).inv)
  exact measurable_const
lemma freight (i : Coat.Stream c f)(p:ℕ)(H : Cash W s μ L Q o C T R) (h:∀ (F:Forest S.ratio)(X:Coat T F), X.x=s → X.width=o.K → ContDiffAt ℝ p (meanV X i) 0): Kept H (H.supportP (identityLog (.inr (.inl (.inl i))))) (fun _ X _=> delta p i R X) :=by
  have he:= H.laws.data.room; have ha:= H.laws.data.access; let o':=rowSite S i; let J:= Canvas.primary G
  constructor
  · intro F X X' w v hx hK Z hv hp hh; subst s
    let A : Borough X X' Z w v ∅ ∅ R := ⟨hp,(observe _).1 hh,fun _ _=>Iff.rfl⟩
    have hh:Cleanroom Z (400*X.B) o':=fun j hj=> hv ((Animals.neighbors_mem ..).2 (hj.trans (Nat.mul_le_mul_right _ (by have hp:=Q.buys; omega))))
    have hS (d) (ht : d≤ 250*X.B):Zone X X' o' d:= A.social (fun i hi=>hh i (by have hx:100≤X.B:=he.sight.1; omega))
    have hP : Inside o' X.seeds (200*X.B) ↔ Inside o' X'.seeds (200*X.B):= (hS _ le_rfl).covert o' (by rw [separation_self];omega)
    have hf := pitch_fence J o' (hS (120*X.B) (by omega)) (lt_of_lt_of_le (by norm_num) he.sight.1)
    unfold Pavilion.delta voltageV tune; rw [← A.B,hf, (A.cornice he i (fun i hi=> hh i (hi.trans (by omega)))).1, show meanV X i=_ from
      funext fun v=> sapped X v _ (hS _ (by omega)) he]; simp_rw [show rowSite S i=o' from rfl,hP]; rfl
  · intro E _ F X ht hw V Y w hV he' hΨ; subst s; have hm : ShellAccess S G X.x W X.width o.γ:= by rw [hw]; exact ha
    let Z t:= drive X (V t) (Y t); let L t:= voltage (Z t)
    have hL:Measurable L:= (compassBro he.accepted hV X he' hm R.beta).1
    have hh : Measurable fun t=> Vine.costs (Z t) (L t) i.1 i.2:= by
      refine Finset.measurable_fun_sum _ fun j _=> ?_; change Measurable fun v=> if X.selected _ _ then _ else 0; split_ifs
      · exact ((((Shield.strains he.accepted hV X he' hm hL i.1 j).norm.pow_const 2).div_const 2))
      exact measurable_const
    change Measurable fun t=> -R.beta*Raw.orientation*((if Inside o' X.seeds (200*X.B) then 0 else _) -(if Inside o' X.seeds (200*X.B) then 0 else blockTaylor p (meanV X i) (pitch J (Z t) o'))); split_ifs
    · exact measurable_const
    exact measurable_const.mul (hh.sub ((blockTaylor_contDiff p (meanV X i) 0).continuous.measurable.comp (fiction J X _ hV)))
  · intro F X ht hw hz z w; subst s; have hr: ShellAccess S G X.x W X.width o.γ:=by rw [hw]; exact ha
    let Y:=sluice X z; unfold Pavilion.delta tune voltageV; rw [awning z X he.accepted hr, show meanV Y i=meanV X i from rfl, footing, blockTaylor_equivariant (h F X rfl hw) (tinters _ _ _) (ContinuousLinearMap.id ℝ ℝ) (Eventually.of_forall fun x=> mean_colored X i x _ he.accepted hr)]; rfl
  intro F X hs hw _ l b d E _ _ _ V x hp hh hψ; subst s
  let Z (t:F.Slice G×Air f G) y:=drive X (V y) t.1
  have hY : Zest (fun t y=> Vine.costs (Z t y) (voltage (Z t y)) i.1 i.2) x l := by
    refine Zest.total _ _ (fun j (_:j∈parents i.2)=>?_); unfold Vine.pot; change Zest (fun t y=> if X.selected _ _ then ‖_‖^2 /2 else 0) x l; split_ifs
    next ht=> exact (hp.fellows _ he (Y:=Prod.fst) (i.1,j) ht (hp.settles (Y:=Prod.fst) he)).wand (p:=fun y:G.Color=> ‖y‖^2/2) ((contDiff_norm_sq ℝ).div_const _)
    exact Zest.still _
  change Zest (fun t y => -R.beta*Raw.orientation*((if Inside o' X.seeds (200*X.B) then 0 else _) -(if Inside o' X.seeds (200*X.B) then 0 else blockTaylor p (meanV X i) (pitch J (Z t y) o')))) x l
  split_ifs; · exact Zest.still _
  obtain ⟨v,hv⟩:=hp.sails; exact (hY.plusminus ((titrates J X o' hv).wand (blockTaylor_contDiff p (meanV X i) l))).scalar (-R.beta*Raw.orientation)

def spinV (H : Cash W s μ L Q o C T R) (p:ℕ) (i:LogIndex c f):Port.Test T:=
  match i with
  | .inr (.inl (.inl k))=> fun F X w=> Canvas.char H p k F X w- delta (p+2) k R X
  | _ => trunk H p i
lemma graduates (v d:ℝ→ℝ)(L:Side)(o:Target.Order G W)(P:Teller G)(Q:YM.ConnectedActivityE6.Target G P) (p i:ℕ)(ζ:ℝ)(hv:Rate G L (-(1/2)) v)(hd:Rate G L (-(1/2)) d)(hu:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G)(χ:Chi) : ∃ b: ℝ→ℝ, Rate G L (-((p:ℝ)+1)/2) b ∧ (∀ x,0≤b x) ∧
    ∀ᶠ s in atTop, ∀(c f':Side)(S:StepData c f')(T:Tube G S)(R:Rep G f')(μ C:ℝ)(H:Cash W s μ L Q o C T R), S.patch=D → Pass H p i (spinV H p) ζ (v s) (d s) 1 (b s) χ:=by
  obtain ⟨K,hK,hN,hP⟩:= freelyBooks v d L o P Q p i ζ hv hd hu D hD χ
  obtain ⟨B,hB,hY⟩:= rootpay P Q o v d L hv hu D hD χ p i
  obtain ⟨Y,_,hX⟩:= landV P Q o v L hv hu D hD (p+2) (by omega)
  refine ⟨fun x=> K x+|B x|, hK.add (hB.compare (Eventually.of_forall fun x=> (abs_abs _).le)),fun x=>add_nonneg (hN _) (abs_nonneg _),?_⟩
  filter_upwards [hu,hY,hX,hP] with x hz hh hp h c f S T R μ C H hS; let p' := p+2
  have ht := h _ _ S T R μ C H hS; have hL i' := freight i' p' H (fun F X he hv=> (hp _ _ S T R μ C H F X i' hS he hv 0 (by simpa using hz)).smooth)
  constructor
  · rintro (i|k|i); exact ht.stamp _
    · rcases k with k|k; swap; exact ht.stamp _
      simp_rw [spinV, sub_eq_add_neg]; exact plusTest (ht.stamp (.inr (.inl (.inl k)))) ((hL k).smooth Neg.neg (by fun_prop))
    exact ht.stamp _
  · rintro (k|k|k) he <;> first| rfl | exact (he k rfl).elim
  intro j; rcases j with j|j; swap
  · exact (ht.round (.inr j)).climb H (le_add_of_nonneg_right (abs_nonneg _)) le_rfl
  intro E _ _ _ F X V u z y w ht' hw hΨ hχ hm hu
  have he:= ht.round (.inl j) E F X V u z y w ht' hw hΨ hχ hm hu
  refine (he.gathering (hh _ _ S T R μ C H j hS E F X V u z y w ht' hw hΨ hχ hm hu)).shimmy (Eventually.of_forall fun t=>?_)
  simp only [Mesh.error, spinV,Canvas.trunk]; abel

def graded (G:Gauge): Regime G where
  symbol H l i := spinV H l i
  enroll P Q:=by
    refine ⟨0, fun L _ D hD i l χ W _ μ _ o v d hv he hd a b ζ ha hb _=>?_⟩
    obtain ⟨B,hB,hN,hb'⟩:= graduates v d L o P Q l i ζ hv hd he D hD χ
    obtain ⟨V,hV,h⟩:= passport G P Q L o ζ a χ B v d l i (by convert! (((Rate.power (a:=a)).weaken ha).pow l).mul hB using 1; ring) hN
    exact ⟨V,hV.weaken hb.le,(hb'.and h).mono fun x hx c f S T R C H hS _ r hr=> hx.2 _ _ S T R μ C H r _ hr (hx.1 c f S T R μ C H hS)⟩
end YM.LocalTaylorR2.Pavilion
