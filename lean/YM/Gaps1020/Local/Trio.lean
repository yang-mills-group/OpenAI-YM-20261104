import YM.Gaps1020.Local.MenuVac
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared.Post.OfferP
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
-- Include the implicit empty-ticket variant so retaining a nil source still
-- uses the forward Cash and charged Choice Ω. Difference vs A's vacuum
-- filter: no early rejection of CLUSTERS by estimates on head count/travel.
-- Only leaf cut & length, OR order above M. Caption literal integral law
-- exported from B2 applied to this same µ. Core admits **all** post/aux
-- Embrasures (Ports without W-collisions) on one Factor.
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves Gas Ursell Captain
open AnalyticBridge VerifiedReset Collection Extra.Iteration Quotes Song Match Geo


open PhysicalNext.Repeat.Lotus
open Slide Rain Trio Boulevard
local notation "η" => MeasureTheory.Integrable

-- apportion CANONICAL sub-log for each actual and for each Zeal (paired)
-- auxiliary census. Norm first at original large torus for unmasked scalar
-- (`Local` support numbers incl neighbor). Also supply orchard error bound
-- after re-expression using up to ALL auxiliary sites + tilt (not amounting
-- to ALL S). No pointwise estimate on volume derivative of true torus bar.
variable (k:ℕ)
variable (D:BudgetPoint){D':BudgetPoint} {w:ℝ}
set_option quotPrecheck false
local notation "S'" => (Beam.marquee H D).reg
local notation "M₀" => Meadow.panel H k

def pile (H:Cash W s μ L Q o C T R) (f:ℕ→ Config G c→ℝ)(o:Site c):=
    ∑ i∈Meadow.panel H k, Meadow.garnerAt H D o i • f i

variable (f':ℕ→ Config G c→ℝ) (u:Site c)
lemma assemble : froth (pile k D H f')= ∑ i∈M₀, f' i:=by
   unfold froth pile; funext x; simp only [Finset.sum_apply, Pi.smul_apply,smul_eq_mul]; rw [sum_comm]; exact sum_congr rfl fun i _=> by rw [← Finset.sum_mul, Meadow.paysOne,one_mul]
lemma add (g:ℕ→ Config G c→ℝ): pile k D H (f'+g)=pile k D H f'+pile k D H g:=by funext u; simp only [pile,Pi.add_apply, smul_add,Finset.sum_add_distrib]
variable (h : Meadow.Budget D (Beam.marquee H D).reg f' w)(hF:D.B=radiusB s)
include h hF
lemma scalar (V:Config G c)(he:RG.flags D.threshold V=∅): ‖pile k D H f' u V‖ ≤ (ballCost (Meadow.studio Q.halo (radiusB s)):ℝ)*w:= by
  let K:= (Meadow.studio Q.halo (radiusB s)); let S:= neighbors K u; let f:= pile k D H f' u
  obtain ⟨t,ht,hT⟩:=h; let y i x:= if (S' i).site=x then t i * Real.exp (preExponent D*coverNumber D.B (S' i).support) else 0
  rw [pile,Finset.sum_apply]; refine (norm_sum_le ..).trans ?_; refine le_trans (b:=∑ i∈M₀,∑ x∈S,y i x) (sum_le_sum ?_) ?_
  · intro i hi; have ht' := Meadow.portions H D u i; have hv := Meadow.nonnegative H D u i; rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg hv]
    by_cases he': Meadow.garnerAt H D u i=0; · rw [he',zero_mul]; exact sum_nonneg fun _ _=> (ht _).1 _
    have he':=(Meadow.assigned H D u i hi hF he').2 ((S' i).anchor); unfold S y
    rw [sum_ite_eq,if_pos he']; apply (mul_le_of_le_one_left (norm_nonneg _) ht').trans
    exact (((hT i).2).2 V (by unfold Healthy;rw [he]; simp) [] (by simp) (by simp)).trans (le_mul_of_one_le_right ((hT i).2.1) (Real.one_le_exp (mul_nonneg (headline D).exponent_pos.le (Nat.cast_nonneg _))))
  rw [sum_comm]; have hv:= Finset.sum_le_sum (s:=S) (fun x (_:x∈S)=> budget_sum (ht x) M₀); have hs: S.card ≤ ballCost K:= neighbors_card ..; refine le_trans hv ?_; rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (budget_nonneg (ht 0))
omit hF
lemma prices :
   let Y:= Boulevard.stillA (Trio.froth (pile k D H f'))
   D.Regular univ Y ∧ ∀ V, RG.flags D.threshold V=∅ → ∀ l:List (Directions G c),l.length ≤ D.order → (∀ i∈l, ‖i‖ ≤ D.threshold)→ ‖leftDerivs Y l V‖ ≤ 2* (Fintype.card (Site c):ℝ)*w :=by
   intro Y
   obtain ⟨a,ha,hf⟩:=h; have ht : SumBudget a ((Fintype.card (Site c):ℝ)*w):= planetary ha (fun x=> (hf x).2.1)
   let y:= froth (pile k D H f')
   have h : y= ∑ i∈ M₀,f' i:= assemble ..
   have he:D.Regular univ y:= by rw [h]; exact Meadow.regularA _ fun i hi=> CouplingShape.reg_extend (hf i).1 (Finset.subset_univ _)
   have hh V (hV:RG.flags D.threshold V=∅) (l:List (Directions G c)) (hh:l.length≤D.order) (hx:∀ i∈l,‖i‖≤ D.threshold): ‖leftDerivs y l V‖ ≤ (Fintype.card (Site c):ℝ)*w:=by
      have h' i: Healthy D.threshold i V:=by unfold Healthy; rw [hV]; simp
      rw [h,Push.Local.left_sum _ _ V l _ hh]; apply (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (s:=M₀) ?_) (budget_sum ht M₀)); exact fun i _=> ((hf i).2).2 V (h' _) l hh (fun i hi=> tiny (hx i hi) _)
      exact fun i _=> (hf i).1.smooth _ (h' _)
   let z (U:Config G c):= y 1
   refine ⟨reg_sub he (CouplingShape.reg_const _), fun V h l hl hx=>?_⟩
   have h1: ‖y 1‖ ≤ (Fintype.card (Site c):ℝ)*w:= hh 1 (smoky («P»:=D) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read,posDir,negDir] using D.threshold_pos)) [] (by simp) (by simp)
   have ht: ‖leftDerivs z l V‖ ≤ ‖y 1‖:= by cases l <;> simp only [z,Work.G07.left_const]; all_goals simp
   change ‖leftDerivs (y-z) l V‖ ≤ _; rw [VerifiedReset.left_sub (he.smooth _ (by unfold Healthy;rw [h]; simp)) (show Push.Local.Chart D.order z V from contDiffAt_const) hl]; exact ((norm_sub_le ..).trans (add_le_add (hh _ h l hl hx) (ht.trans h1))).trans_eq (by ring)
-- general ornament transfer WITHOUT need represent tiny. all Flag, Slide.
omit h
variable {Y':Stars→Side} (A:∀ i:Stars,(Y' i).val=2*(k+i.val)) (F:∀ i:Stars,Trio.Offer G (Y' i))(p:Stars→ℝ){B:ℕ}
lemma stitch (h:∀ i,D.Regular univ (Boulevard.stillA (Trio.froth (F i))) ∧ ∀ V, RG.flags D.threshold V=∅ → ∀ l:List (Directions G (Y' i)),l.length ≤ D.order → (∀ z∈l,‖z‖≤ D.threshold)→ ‖leftDerivs (stillA (Trio.froth (F i))) l V‖ ≤ p i) (hB:k+4 ≤ B) (hp:∀ i,0≤p i):
    D.Regular (neighbors B u) (Trio.ornament A F u)∧ D.supBounds u (neighbors B u) (Trio.ornament A F u) (Trio.oroW D B p):=by
   rw [Trio.orchard]; let g i:=Boulevard.stillA (Trio.froth (F i)); let O:=Trio.pad A
   have hv i (j:Site (Y' i)): separation u (Slide.sites (pad A i) u j) ≤ B:= (Slide.village (w:=k+i.val) (A i).ge _ j).trans (by have hh:=i.isLt; omega)
   have hs (i:Stars)(h':i∈ (univ:Finset Stars)): D.Regular (neighbors B u) (Slide.ray i • (g i∘Slide.shape (O i) u)):= CouplingShape.reg_scale _ (Slide.regular (O i) u (h i).1 fun j=> (neighbors_mem ..).2 (hv i j))
   refine ⟨Meadow.regularA _ hs,Trio.sup_S D _ _ _ _ _ hs (fun i _=> CouplingShape.sup_scale _ ?_)⟩
   refine ⟨mul_nonneg (show 0≤Trio.tilt D B from by unfold Trio.tilt; positivity) (hp i),fun V h' l hl hv'=>?_⟩
   let X:= Slide.shape (O i) u V
   have hK:= Trio.hint (B:=D) A B V i hB u h'
   exact Slide.stalled (O i) u (g i) (hv i) l V hl hv' ((h i).1.smooth _ (by unfold Healthy; rw [hK]; simp)) ((h i).2 _ hK)
lemma adjoin (C:∀ i:Stars,Trio.Offer G (Y' i)): Trio.ornament A (F+C) u=Trio.ornament A F u+Trio.ornament A C u:=by funext V; simp only [Pi.add_apply,ornament,beacon,unit,rip,Boulevard.stillA]; simp_rw [add_sub_add_comm, Finset.sum_add_distrib,mul_add, Finset.sum_add_distrib]
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared.Post.OfferP
