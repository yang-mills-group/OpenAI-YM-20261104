import YM.RGLocalTaylor.Retain.Cameo
/-! # Pay after Turns and tapestry operations on common stencil and orientation
K data stays true. Identify all invariant grade splits for transported U.
All Tough, Hats, Scroll & source partners at ORIGINAL subsidized frames,
 not shifting due to orientation or Reads here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt RG01.Survive
open Mayer goodK Mill
open Match Song Push AnalyticBridge VerifiedReset Collection Extra.Iteration Refrain Geo Quotes
open Captain Ursell Gas Brim
open Fort
open RGLocalTaylor.Read
namespace Gorge
variable {f₁ f₂ : Post.glyph G f} {M:ℕ} (H) (X :Cash W s μ L Q o C T (impulse R f₂ a))
    {Ξ : Utopia H j v d r C' χ} {N : Captain H j C' d v Y A b r B q n χ}
    (p : BudgetPoint) (i : ℕ) {δ β w : ℝ} {z z':H.fragrances}
set_option quotPrecheck false
local notation "κ" => Opacity.key S
local notation "χM" => cover H (physical H M) (χ:=χ)
local notation "ψM" => cover H (mantle H f₁ M) (χ:=χ)

-- predicate splits at arbitrary linear filter (`Start` known only ahead.V)
variable (p₁ p₂ p₃:H.fragrances→ℕ→Prop) (v':Expansions H M)
lemma field_join (ht:∀ p q,(p₁ p q ∨ p₂ p q)↔p₃ p q)(hh:∀ p q,¬(p₁ p q∧p₂ p q)):
   Read.field p₃ v'=Read.field p₁ v'+Read.field p₂ v':=by
   ext p V; unfold Read.field; simp only [Pi.add_apply]; rw [← mul_add]; apply congr_arg
   simp_rw [Finset.sum_filter]; rw [← sum_add_distrib]; refine Finset.sum_congr rfl ?_
   intro b _; rw [← ht]; split_ifs with h hF hX hv <;> first| exact False.elim (hh _ _ ⟨by assumption,by assumption⟩)| grind

/-- common split all three. -/
def floors (M:ℕ)(_x: H.fragrances)(p:ℕ): Prop:= ¬ M+1 ≤ p
def base0 (_x:H.fragrances) (p:ℕ):Prop:=p≤1
def nextG (M:ℕ)(x:H.fragrances)(i:ℕ):Prop:=2 ≤ i ∧ floors H M x i
local notation "sM" => floors (H:=H) M
local notation "hM" => nextG (H:=H) M
local notation "U'" => RPC H f₂ (χ:=χ)
variable (Θ: Stencils T M)

lemma at_two (ht:M≥1) : Read.field sM (cover H Θ (χ:=χ))=Read.field (fun _ i=>i=1) (cover H Θ (χ:=χ))+ Read.field hM (cover H Θ (χ:=χ)):=by
   have hh(f:H.fragrances)(i:ℕ): (i=0 ∨ (i=1∨ nextG H M f i)) ↔ floors H M f i:=by unfold floors nextG floors; omega
   let U:=fun q k=> k=1∨ nextG H M q k
   let X := (cover H Θ (χ:=χ)); change Read.field sM X=_; rw [field_join H (fun _ i=>i=0) U sM X hh (by intro i d; unfold U nextG; omega), show Read.field (fun _ i=>i=0) X=0 from dialect H Θ,zero_add, field_join H (fun _ i=>i=1) (nextG (H:=H) M) U X (fun _ _=>Iff.rfl) (by intro i d; unfold nextG; omega)] -- quote; edit

section spiral
variable {V:Rep G f}{J : Cash W s μ L Q o C T V}(Y' : Match.Alliance J H 1 0)(Y₀ : Match.Alliance J X 1 0)
  (hy : Y'.units= Equiv.refl _)

abbrev stamp (f:H.fragrances→ Config G c→ℝ) : ℕ→ Config G c→ℝ:= Song.choir (Gorge.stencil Y' f) ∘ pennant J
local notation "St" => stamp H Y'
local notation "W'" => Beam.marquee J p
local notation "LP" => orient p (Beam.marquee J p).reg
variable {f' g : H.fragrances → Config G c→ℝ}

lemma log_add (f g : H.fragrances → Config G c→ℝ): St (f+g)= St f + St g:= by
  have hp (i:ballad J) V : Song.choir (Gorge.stencil Y' (f+g)) i V= Song.choir (Gorge.stencil Y' f) i V+ Song.choir (Gorge.stencil Y' g) i V:= by
     rcases i with ⟨i,j|j⟩
     · unfold Song.choir Gorge.stencil; simp_rw [Pi.smul_apply, smul_eq_mul]; simp [Function.comp_apply]; ring -- simp may solve
     change _ * (0:ℝ) = _*0+_*0; ring
  funext i V; exact hp (pennant J i) V
lemma log_sub (f g : H.fragrances → Config G c→ℝ): St (f-g)= St f- St g:= by apply eq_sub_of_add_eq; rw [←log_add H Y' (f-g),sub_add_cancel]
lemma stampS (f:Magazine J→ Config G c→ℝ):
   Song.choir (a • f) ∘ pennant J = a • (Song.choir f ∘ pennant J) := by
   ext i V; change _ * (a * (f (pennant J i).2 ..))=a*((Song.Rim c)*_); exact mul_left_comm ..

include hy
-- any *row* restriction RPC.Support. from proxy price after Translating
omit hy in
lemma picked (h:LP (St f') w) (hp:∀ i, g i=f' i ∨ g i=0) : LP (St g) w:= by
   refine Meadow.emptyFree (p:=p) (u:=St f') _ h (St g) (fun i=>?_); unfold stamp
   let T:= pennant J i; change (Song.Rim c • (Gorge.stencil Y' _ T.2 ∘ T.1.view) = Song.Rim c • (Gorge.stencil Y' _ T.2 ∘ T.1.view) ∨ Song.Rim c • (Gorge.stencil Y' _ T.2 ∘ T.1.view) =0)
   rcases hx:T.2 with x|x
   · rcases hp (Y'.furrow x) with he|he
     · left; change Song.Rim c • ((-1:ℝ) • f' (Y'.furrow x) ∘ T.1.view)=_ -- orientation group
       rw [←he]; rfl
     right; ext V; change _ *((-1:ℝ) * _)=0; rw [he]; simp
   exact Or.inl rfl
-- anchor supplied Seat: full icon stream has the actual costs even in offshoot.
def onlyLit (H : Cash W s μ L Q o C T R)(χ:Chi): H.fragrances→ Config G c→ℝ:= iconOnly H (fun i V=> stream H χ V i)
lemma broadcast (h : Collection.Local W' p (Height.serve J Y' χ (Beam.lit J)) w δ) : orient p (Beam.marquee J p).reg (St (onlyLit H χ)) w:= by
   obtain ⟨g,hG,hU⟩:= h.cheap; refine Meadow.emptyFree (p:=p) (u:= (Height.serve J Y' χ (Beam.lit J)).logRead) _ ⟨g,hU,fun i=> ⟨h.smooth i,hG i⟩⟩ _ (fun i=> ?_)
   let t:= pennant J i; let f(i:H.fragrances):= onlyLit H χ i
   change Rim c • (Height.skilled J Y' χ (Beam.lit J) t.2 ∘ t.1.view)=Rim c • (Gorge.stencil Y' f t.2 ∘ t.1.view) ∨ Rim c • (Gorge.stencil Y' f t.2 ∘ t.1.view)=0
   rw [Height.pivot _ _ _ _ 0]; rcases hx: t.2 with y|y
   · by_cases h: y ∈ Set.range (icon J)
     · rw [if_pos (show Height.chosen J (Beam.lit J) (Sum.inl y) from Or.inr h)]; left; ext V; change Rim c * ((-1:ℝ)* _)=Rim c*((-1:ℝ)* f (Y'.furrow y) _); obtain ⟨v,hv⟩:= h; unfold f onlyLit iconOnly; rw [if_pos (show _ ∈ Set.range (icon H) from ⟨v, (hv ▸ (Beam.mimics J Y' hy v).symm : icon H v= Y'.furrow _)⟩)]
     right; ext V; change Rim c*((-1:ℝ)* f (Y'.furrow y) _)=0; unfold f onlyLit iconOnly; rw [if_neg (show Y'.furrow y∉ Set.range (icon H) from by rintro ⟨v,hv⟩; exact h ⟨v,Y'.furrow.injective ((Beam.mimics J Y' hy v).trans hv)⟩)]; simp
   right; change Rim c • ((0:Config G c→ℝ)∘t.1.view)=_; ext; simp

-- choose unmark first strum via proxy with Career.AP. Need prove all Terms Price.L.P from general dorm.
end spiral

section plus
variable (W: ℕ→RegularAddress c) {f g:ℕ→ Config G c→ℝ}
lemma adds (h:orient p W f r)(he:orient p W g a): orient p W (f+g) (r+a):= by
  obtain ⟨u,hU,hp⟩:=h; obtain ⟨v,h,hv⟩:=he
  refine ⟨u+v,fun i=>?_,fun i=>?_⟩
  · convert budget_plus (hU i) (h i) using 2 with j; dsimp only [Pi.add_apply]; split_ifs <;> ring
  have hh:(f+g) i=f i-((-1:ℝ) • g i):= by simp
  rw [hh]; refine ⟨CouplingShape.reg_sub (hp i).1 (CouplingShape.reg_scale (-1) (hv i).1),?_⟩
  have hM':=CouplingShape.sup_scale (-1) (hv i).2; rw [abs_neg,abs_one,one_mul] at hM'; exact CouplingShape.sup_sub (hp i).1 (CouplingShape.reg_scale (-1) (hv i).1) (hp i).2 hM'
lemma scales (h:orient p W f r)(he:0≤a): orient p W (a • f) (a*r):=by
  obtain ⟨u,hM',hV⟩:=h; refine ⟨fun i=>a*u i,fun i=>?_,fun i=> ⟨CouplingShape.reg_scale a (hV i).1,?_⟩⟩
  · convert! budget_scale he (hM' i) using 2; rename_i i;dsimp only; split_ifs <;> ring
  simpa only [abs_of_nonneg he] using! CouplingShape.sup_scale a (hV i).2
end plus
end Gorge
end Retain
end YM.RGLocalTaylor
