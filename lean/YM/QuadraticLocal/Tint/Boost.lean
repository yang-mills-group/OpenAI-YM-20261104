import YM.RemainderComparison.Creek.Observatory
/-!
# qlocal—Additional seam classifiers and propagated relative errors

Extends proof from `Creek.Observer` on the same actual footprint. Keep
 signed residual markers, with the indicated boost at their OWN Paint witnesses,
 along with longitude tolls on opaque old vacuum. Estimate does not assert
 any cheap long-test memory locality on Admission; we require the before-L
 width constraints etc when paying at stencils. Boost can apply to ANY
 footprint weighting, not just the `pigment` Lens and not requiring Open parameter
 extension to the physical density. Thus can keep relative old Mark error factors
 while allowing a separate budget for untouched long-path refurbishing.

 A real input with zero stamp budget, use any upper provision if needed; for
 *this* reading don't throw away its weight behind a non-normalized representation.
 Always processor.Stamps.L.Real.Flag.Halo.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Creek
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι β : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet Serif Typeface
variable (U:Pad H j χ)
local notation "P₀"=> tax G L x
variable {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)(Z:Set ι)(δ:ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l δ H τ K Y I)
local notation "Lt"=> sits Z l δ
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable [DecidableEq β]{Jm:Marker.Census β}
variable (z:ι→Marker.Poly Jm) {gP:β→ℝ} (hZ : Chorus Jm gP Z z k)
open Mallow Ovens Progress.DirectedRecipe
open WickReps
local notation "Tt"=> Sleet.Staff Vx H
local notation "Σ₁" => Mosaic.etude Vx H χ
local notation "Σ₂" => Mosaic.etude Vy H χ
open Mosaic Serif
local notation "A₀" => theater H χ M x' l Z δ
local notation "Rt" => Flues.candle M x' S
variable (P':BudgetPoint)(hx:P'.B=radiusB x)(ht:P'.threshold=Pressure.temp x)(hp:P'.order≤j)(hJ:P'.power≤J)
open Verse
local notation "Ac₀"=> Academy H χ M x' l Z δ k
set_option quotPrecheck false
local notation "mkq" => (A₀).marks
variable {Vb C': Set (Staff (brand M x') H)}
local notation "pureV"=> Muse.Pure Vx H χ Z k
local notation "impur" => Muse.impure Vx H χ Z k
local notation "S*" => spare H χ M x' l Z δ
local notation "U'"=> Muse.song Vx H χ U.V (∅:Set ℕ) 0
variable (E:Set ℕ) (F':Set ℕ)(H':Set ι)
namespace Ezra
variable (f' g:ℝ)(H₂:Set ι) (hz:0 < f')(ht':0 < g) (hg:f' ≤ 1)(ha:g ≤ 1)
local notation "p₁"=> rage H' f' l
local notation "bT"=> theater H χ M x' (p₁) Z δ
variable (hy:Motto (brand M x') (rage H' f' l) δ H τ K Y I)
include h hx ht hp hJ hy hz hg
lemma pushed : Manor.Spinal A₀ {p:Tt| pureV p∧ humid H M x' H' p} Rt P' a (f'*(Y^k*γ)):=by
   obtain ⟨f,hf,hB,hx⟩:= (mass₀ H χ U M x' p₁ Z δ h hy P' hx ht hp hJ).grants
   let w i:= f'*f i; have he i : 0 ≤ w i:= mul_nonneg hz.le (hf _)
   have hS i (hp:pureV i) (hF : humid H M x' H' i) y: P'.Regular ((bT).halls i) ((A₀).solvent y i) ∧∀ x∈ (A₀).halls i, P'.supBounds x ((A₀).halls i) ((A₀).solvent y i) (w i):=by
        rw [Creek.solvent H χ M x' l Z δ H' i _ y hz]; refine ⟨AnalyticBridge.CouplingShape.reg_scale _ ((hB i hp).1.angle _),fun x hx=> Manor.Stem (AnalyticBridge.CouplingShape.sup_scale _ ((hB i hp).2 _ x hx)) ?_⟩
        rw [abs_of_pos (pow_pos hz _)]; apply mul_le_mul_of_nonneg_right _ (hf _)
        exact (pow_le_pow_of_le_one hz.le hg (lustre H χ M x' l Z δ H' i hF)).trans_eq (pow_one _)
   refine ⟨w,he,fun i ⟨hp,hh⟩=>⟨Creek.symmetry H χ M x' l Z δ P' (fun z=> (point H χ M x' p₁ Z δ _) ▸ (hS i hp hh z).1),fun z=>(hS i hp hh z).2⟩, fun i=> ?_⟩
   exact AnalyticBridge.VerifiedReset.Quotes.hit_scale hz.le hx i
local notation "gq"=>gStep R.beta
variable (W':Wand H χ M x' l Z δ n k s E ∅ (H'∪H₂) Vb) (wp:ℕ→ℝ)(hW: Halo.Presents R E wp Gp) (htG: Gp ≤ incomingE G L x) (hgT:Motto (brand M x') (rage H₂ g l) δ H τ K Y I)
include W' wp hW hh ht' ha htG hgT
lemma glance :
    Manor.Spinal A₀ ({p|p∈ Ac₀ ∧ pureV p∧ ¬ Halo.dyed Vx H E p.1 p.2} \ Vb) Rt P' a (2*gq^s+(f'+g)*(Y^k*γ)):=by
   let L' (p:Staff Vx H):Prop:= Halo.dyed Vx H ∅ p.1 p.2
   have hy':= pushed H χ U M x' l Z δ h P' hx ht hp hJ H' f' hz hg hy
   have h₀:=pushed H χ U M x' l Z δ h P' hx ht hp hJ H₂ g ht' ha hgT
   have hz := tradition H χ U M x' l Z δ h hh P' hx ht hp hJ ∅ 0 0 (Halo.Presents.zeroG _) ((Halo.Presents.positive hW).trans htG)
   have hp' := prior (a:=a) (u:=gStep R.beta^s) (Vb:={p|pureV p ∧ tumble H p.1}) H χ M x' l Z δ P' (fun y=> (Typeface.ally H χ U M x' y l Z δ h hh P' hx ht hp hJ).1)
   have hh' := prior (a:=a) (u:=gStep R.beta^s) (Vb:={p|pureV p ∧ Flurry H p.fst k s}) H χ M x' l Z δ P' (fun y=> (Typeface.ally H χ U M x' y l Z δ h hh P' hx ht hp hJ).2.1)
   let bB:= {p | p∈ Ac₀ ∧ pureV p ∧ ¬ Halo.dyed Vx H E p.1 p.2 ∧ p∉Vb ∧ ¬ L' p ∧ ¬ humid H M x' (H'∪H₂) p ∧ ¬ Flurry H p.1 k s∧ ¬ tumble H p.1}
   have hr0 : Manor.Spinal A₀ bB Rt P' a 0:=by
       refine ⟨fun _=>0,fun _=> le_rfl,?_,fun i=> ?_⟩
       · intro p ⟨h₁,h₂,hV,hi,hH,hL,hK,h⟩; have ht (y:α): (A₀).solvent y p= fun _=>0:=by
             funext V; change _*string (brand M y) H χ p.1 p.2 V=0; by_contra he
             apply hi (W'.intake p h₁ h₂.1 hV hH hL ⟨y,?_ ,V,right_ne_zero_of_mul he⟩)
             refine Sleet.season (brand M y) H χ p.1 p.2 E (right_ne_zero_of_mul he) ?_ hK h ?_ hV
             · rintro ⟨i,hv',he⟩; apply hL ⟨i,hv',?_⟩; change Sleet.shade R n ((Vx i).turn) at he; unfold Sleet.shade at he; split at he
               next i' hq=> exact W'.loyal i i' hq he
               next=>contradiction
             rintro ⟨i,j,⟨z,hz,h'⟩,hj⟩; exact hH ⟨i,j,⟨z,W'.vested hz,h'⟩,hj⟩
         refine ⟨Creek.symmetry H χ M x' l Z δ P' (fun x=>?_),fun y z _=>?_⟩
         · rw [ht x]; exact AnalyticBridge.CouplingShape.reg_const (0:ℝ)
         rw [ht y]; simpa only [abs_zero] using! AnalyticBridge.CouplingShape.sup_const (G:=G) (p:=P') (o:=z) (X:=(A₀).halls p) (0:ℝ)
       apply budget_of_sum _ (fun s=>?_)
       · intro i; split <;> simp
       simp
   have hv := ((((hp'.swell hh').swell (hy'.swell h₀)).swell (hz.skim (Set.Subset.refl _) (show _≤0 by rw [mul_zero]) le_rfl)).swell hr0)
   apply hv.skim ?_ (by apply le_of_eq; ring) le_rfl
   intro p ⟨⟨hi,h,hP⟩,hp⟩
   by_cases hz : L' p; exact Or.inl (Or.inr ⟨h,hz⟩)
   by_cases hx : humid H M x' H' p; exact Or.inl (Or.inl (Or.inr (Or.inl ⟨h,hx⟩)))
   by_cases h₀ : humid H M x' H₂ p; exact Or.inl (Or.inl (Or.inr (Or.inr ⟨h,h₀⟩)))
   by_cases he' : tumble H p.1; exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h,he'⟩)))
   by_cases he'': Flurry H p.1 k s; exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h,he''⟩)))
   refine Or.inr ⟨hi,h,hP,hp,hz,?_,he'',he'⟩
   rintro ⟨i,he,hh|hh⟩; exact hx ⟨i,he,hh⟩; exact h₀ ⟨i,he,hh⟩
lemma shears : Manor.Spinal A₀ (Ac₀ \ Vb) Rt P' a (2*gq^s+(f'+g)*(Y^k*γ)+V*Gp+Y^k*Y*γ*δ):=by
   have he := Ezra.glance H χ U M x' l Z δ h hh P' hx ht hp hJ E H' f' g H₂ hz ht' hg ha hy W' wp hW htG hgT -- args check
   apply ((he.swell (tradition H χ U M x' l Z δ h hh P' hx ht hp hJ E wp _ hW htG)).swell (mass₁ H χ U M x' l Z δ h hh P' hx ht hp hJ)).skim ?_ le_rfl le_rfl; rintro p ⟨h,hp⟩; rcases monastery H χ M x' l Z δ h with hV|hV
   · by_cases hh:Halo.dyed Vx H E p.1 p.2; exact Or.inl (Or.inr ⟨hV,hh⟩); exact Or.inl (Or.inl ⟨⟨h,hV, hh⟩,hp⟩)
   exact Or.inr hV
end Ezra
end YM.RemainderComparison.Creek
