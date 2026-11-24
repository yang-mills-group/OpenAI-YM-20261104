import YM.LocalTaylorR2.Mesh.Classroom
import YM.LocalTaylorR2.Canvas.Lilac
/-! # Full principal argument script so far in this book. Freeizes mean here. -/
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
variable {D : ℕ} {o0 : Site c} {V : Config G c} {s p : ℝ}
open Axial Channel
variable {R: Rep G f}{b a γ W α y' ζ d v q μ u C :ℝ}{χ:Chi}{j i' l :ℕ}
variable {Q:YM.ConnectedActivityE6.Target G P}{o:Target.Order G W}{H : Cash W s μ L Q o C T R}
open Port Mesh Animals Itinerary Reserves
-- isolate analytic model at symbols. This constructor can be used again for further upgrades at single-letter (without exposing extra duplicated control recurrences for all other Letter varieties; authorized Crib).
structure Pass (H: Cash W s μ L Q o C T R)(p:ℕ) (k:ℕ)(K: LogIndex c f→Port.Test T) (ζ v d θ U :ℝ)(χ: Chi):Prop where
  stamp : ∀ i, Kept H (H.supportP (identityLog i)) (K i)
  extra (i:LogIndex c f) (_z:∀ k:Miniature c f, i≠ .inr (.inl k)) : K i=weightLog H i
  round : ∀ i:Miniature c f, Sees H k v d χ (Mesh.error K H (.inr (.inl i))) U θ

lemma passport (G:Gauge)(P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(o:Target.Order G W)(α a:ℝ)(χ: Chi) (U : ℝ→ℝ)(v d:ℝ→ℝ)(p i:ℕ) (ht:Rate G L (-(1/2)) (fun x=>(betaF G x L^a)^p * U x))(he:∀ x,0≤ U x) : ∃ f : ℝ→ℝ, Rate G L (-(1/2)) f ∧ ∀ᶠ s in atTop, ∀(c f':Side)(S:StepData c f')(T:Tube G S)(R:Rep G f')(μ C:ℝ)(H:Cash W s μ L Q o C T R)(r:ℝ)(K: LogIndex c f'→Port.Test T), 1≤r → Pass H p i K α (v s) (d s) 1 (U s) χ→ ∃ w, Meter (H:=H) K p α r (v s) (d s) (betaF G s L^a) (f s) i χ w:=by
  -- as in tempo, don't require a hypothesis on v and d here as well as the Pass
  let A x:= (betaF G x L^a)^p*U x
  let m:= Fintype.card Signed*Census.spots L+(Itinerary.density L+ Itinerary.density L)
  let b x:= ((Animals.ballCost ((Q.halo+1)*radiusB x):ℝ)*m)*(A x*Real.exp (Q.relative*Animals.ballCost (Q.halo+1)))
  have hv:=Census.width_rate G L (Q.halo+1) 0; simp only [add_zero] at hv
  refine ⟨b,by simpa only [zero_add] using! (hv.mul_right m).mul (ht.mul_right _),?_⟩
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 0] with x hX c f S T R μ C H r K h ht
  have hx:= H.laws.data.funds.length_eq; have hy:= H.laws.data.room
  have hs: 0<betaF G x L^a:=by positivity
  have he:0≤A x:=mul_nonneg (pow_nonneg hs.le _) (he _)
  have hl := YM.ConnectedActivityE6.fixed (ε:=Q.ε) (C:=A x) (smallCensus S L hx) (show 0<radiusB x from lt_of_lt_of_le (by norm_num) hy.sight.1) _ (packed S (l:=Q.halo) (lt_of_lt_of_le (by norm_num) hy.sight.1)) (show 0≤Q.relative by unfold Target.relative;linarith [Q.usable,Q.bound,Q.pos]) he
  let d':=Sum.elim (fun _ : LogLetter c f=> (0:ℝ)) (Sum.elim (fun _ :Miniature c f=> A x) (fun _ : ChainIndex f=> (0:ℝ)))
  refine ⟨d',ht.stamp,?_,fun j=>?_⟩
  · have hz:= (free (Raw.space T Q.halo (radiusB x) R) (Raw.extra T R) (radiusB x) Q.relative Q.ε).together (hl.together (free (basisFoot S (radiusB x) Q.halo) (basisCharge f) (radiusB x) Q.relative Q.ε)); rw [zero_add,add_zero] at hz
    convert hz using 1; · rfl
    · funext j; rcases j with j|j|j <;> simp only [leaseLog,d',Sum.elim,mul_zero,Real.rpow_zero, one_mul]
    rfl
  have hb : 1 ≤ r * spanW T R (radiusB x) Q.halo (identityLog (S:=S) j):= one_le_mul_of_one_le_of_one_le h (le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  rcases j with j|j|j
  · intro G _ _ _ F X Y u z y Z _ _ _ _ _ _; simp_rw [Mesh.error,ht.extra (Sum.inl j) (by simp),sub_self]; exact (certified (zero_le_one.trans hb) (0:ℝ)).climb (by simp [d']) le_rfl
  · apply (ht.round j).climb H _ hb; apply le_of_eq; simp [d',A,hs.ne',mul_comm ((betaF G x L^a)^p)]
  intro G _ _ _ F X Y u z y Z _ _ _ _ _ _; simp_rw [Mesh.error,ht.extra (Sum.inr (Sum.inr j)) (by simp),sub_self]; exact (certified (zero_le_one.trans hb) (0:ℝ)).climb (by simp [d']) le_rfl

def char (_H: Cash W s μ L Q o C T R)(p:ℕ) (i : Coat.Stream c f) : Port.Test T := fun _ X w=> pineCone (primary G) X o.a R i (p+2) (worldZ X R.beta w)
lemma pick (P:Teller G) (D:Patch)(L:Side)(hD:D.Branches P.bind G) (p:ℕ) :
    ∀ᶠ s in atTop, ∀ (c f:Side) (S: StepData c f) (T:Tube G S)(R:Rep G f)(Q:YM.ConnectedActivityE6.Target G P)(W μ C:ℝ)(o:Target.Order G W)(H:Cash W s μ L Q o C T R)(i:Coat.Stream c f), S.patch=D → Kept H (H.supportP (identityLog (.inr (.inl (.inl i))))) (char H p i):=by
  obtain ⟨ρ,hρ,hL,K,hK,hT⟩:=growth P L D hD (p+2)
  filter_upwards [hT] with x hx c f S T R Q W μ C o H i hD; have hh:=H.laws.data; have he:=hh.room; have ht:=hh.funds.length_eq; have hR:= H.laws.intake.positive
  constructor
  · intro F X X' w v hs hK Z he' hk hC; subst x; exact dyes ⟨hk,(observe _).1 hC,fun i (_:S.ratio.parent i ∈ Z)=> (Iff.rfl (a:=i∈Contract.covered R ∅))⟩ he i Q.buys he' hR
  · intro E _ F X hX hK V u z hp hq hΨ; subst x; exact Canvas.born _ he (X:=X) (show ShellAccess S G X.x W X.width o.γ from (by rw [hK]; exact hh.access)) i hp hq hΨ
  · intro F X hs hw hJ z w; subst x; apply elevation (primary G) X R z he.accepted (show ShellAccess S G X.x W X.width o.γ from (by rw [hw]; exact hh.access)) i
    exact (hx _ _ S T hD ht he i.2 _ 0 (by simpa using hρ.le)).smooth
  intro F X hs ht' hk j b A E _ _ _ V x' hp hm hC; subst x; exact Canvas.braced (primary G) he hp hm (mul_pos o.large he.fiery) (by unfold Coat.t; rw [ht]; exact hC) i hR

def trunk (H: Cash W s μ L Q o C T R)(p:ℕ) (i:LogIndex c f): Port.Test T :=
  match i with
  | .inr (.inl (.inl i)) => char H p i
  | _ => Mesh.part H p i
lemma freelyBooks (v d:ℝ→ℝ)(L:Side)(o:Target.Order G W)(P:Teller G)(Q:YM.ConnectedActivityE6.Target G P) (p i:ℕ)(ζ:ℝ)(hv:Rate G L (-(1/2)) v)(hd:Rate G L (-(1/2)) d)(hu:∀ᶠ x in atTop, 0≤v x)(D:Patch)(hD:D.Branches P.bind G)(χ:Chi) : ∃ b: ℝ→ℝ, Rate G L (-((p:ℝ)+1)/2) b ∧ (∀ x,0≤b x) ∧
    ∀ᶠ s in atTop, ∀(c f':Side)(S:StepData c f')(T:Tube G S)(R:Rep G f')(μ C:ℝ)(H:Cash W s μ L Q o C T R), S.patch=D → Pass H p i (trunk H p) ζ (v s) (d s) 1 (b s) χ:=by
  obtain ⟨U,hU,hN,hp⟩:= errorLaw Q.table Q.table_exists o.a d hd p i χ
  obtain ⟨K,hK,h⟩:= ordinance G L (primary G) P v d hv hd hu χ p i W o D hD
  refine ⟨fun x=> |K x|+ U x,(hK.compare (Eventually.of_forall fun x=>(abs_abs _).le)).add hU, fun x=> add_nonneg (abs_nonneg _) (hN _), ?_⟩
  filter_upwards [hp,h,pick P D L hD p] with x ht hv he c f S T R μ C H hS
  refine ⟨fun i=>?_,fun i hi=>?_,fun j=>?_⟩
  · rcases i with i|(i|i|i)|i <;> first | exact he _ _ S T R Q W μ C o H i hS | exact control (p:=p) H _
  · rcases i with i|i|i <;> try rfl
    exact (hi i rfl).elim
  have ht j:= ht _ _ S T W μ C P Q o R H rfl rfl (v x) j|>.climb H (le_add_of_nonneg_left (abs_nonneg (K x))) le_rfl
  rcases j with j|j|j <;> first | exact (hv _ _ S T R μ C Q H hS j).climb H (le_add_of_nonneg_right (hN _)) le_rfl | exact ht _

def basics (G:Gauge): Regime G where
  symbol H l i := trunk H l i
  enroll P Q:=by
    refine ⟨0, fun L _ D hD i l χ W _ μ _ o v d hv he hd a b ζ ha hb _=>?_⟩
    obtain ⟨B,hB,hN,hb'⟩:= freelyBooks v d L o P Q l i ζ hv hd he D hD χ
    obtain ⟨V,hV,h⟩:= passport G P Q L o ζ a χ B v d l i (by convert! (((Rate.power (a:=a)).weaken ha).pow l).mul hB using 1; ring) hN
    exact ⟨V,hV.weaken hb.le,(hb'.and h).mono fun x hx c f S T R C H hS _ r hr=> hx.2 _ _ S T R μ C H r _ hr (hx.1 c f S T R μ C H hS)⟩
end YM.LocalTaylorR2.Canvas
