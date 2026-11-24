import YM.QuadraticLocal.SameSlot
import YM.RemainderComparison.Flues.Kettle

/-!
Bind the raw Lyric/Serif atlas to the **same** unmarked addresses and `Hard`, before both
of the `qlocal` mask/regular realignments. Coalescing duplicate addresses is *paid* and exact.
Keep the Census (can further reduce the allowed monomials by that data). Each input mark
must have a square-zero actual argument; we allow it to rely on EVERY other mark in its
nonzero mode (keeping the appropriate origin/spans accordingly); same forced address may be
nontrivial on the unmarked path.

`quiet_lane`: compare the actual forced entry at each address, includes every multiplier;
not merely quiet equality after testing the forced family behind a healthy mask.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Lanes
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe
variable {ι V' : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
variable (U:Pad H j χ) {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l 0 H τ K Y I)
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)
    (P':BudgetPoint)(hp : P'.B=radiusB x) (ht:P'.threshold=Pressure.temp x)
    (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)
variable [DecidableEq V']{Jm:Marker.Census V'}
local notation "Φ" => Poly Jm
variable (z:ι→Marker.Poly Jm) {gP:V'→ℝ} (hZ : Chorus Jm gP Set.univ z k)

include hZ in
lemma silent (p:ι): (z p).part Jm.quiet=0 := by
  have he:= congr_arg (·.part Jm.quiet) (hZ.square p); simp_all only [Poly.quiet_mul, Poly.part_nil,mul_eq_zero,or_self]

private lemma paint_silent {y:Type} (A: Verse ι y) (u:y) (hk:∀ i,(z i).part Jm.quiet=0):
    (A.paint Set.univ l z u).part Jm.quiet=(↑(A.emit 0 u):ℂ) := by
  obtain ⟨p,y⟩:=A; unfold Verse.paint Verse.emit Verse.stock; dsimp only; rw [Poly.part_smul]
  cases p using Multiset.induction_on with
  | empty => simp [Verse.controls]
  | cons i p ih =>
      -- reduce
      simp [Verse.controls,hk, Set.mem_univ]

include hZ U
private lemma poly_paint {I:Type} [Fintype I] (M: I→Leaf R) (g:I→ι) (l:I→ℝ)
    (q:Refrain.Leaf H) (Z:Config G c):
    ((∑ w:Scene M H q.val,(parade M H χ q.val w).paint Set.univ l (z∘g) Z).part Jm.quiet) =
      ↑(shootK M H χ H' D (fun _=>0) (Refrain.visa H' D q) Z) := by
  rw [shootK,stuffed,Mosaic.voyage M H χ U.S.N]; rw [Poly.part_sum,Complex.ofReal_sum]; apply sum_congr rfl; intro w _
  exact paint_silent _ _ _ Z fun i=> silent z hZ _

local notation "XA" => Refrain.read H' D χ E₀ V₀
local notation "HL" => fun y:α => Lane (brand M y) H χ Set.univ l 0 z H' D

lemma quietFoible (p:Finset ι) (i:ℕ) (u:Config G c) :
   (foible (brand M y) H χ Set.univ l 0 z H' D p u i).part Jm.quiet=(((XA).K i u):ℂ):=by
  let S':= S; let g := RemainderComparison.Script.restrict p
  let A':= Refrain.visa H' D
  let x0 := Vy ∘ g
  have he (p':Finset ι) : (RemainderComparison.Script.restrict p') ⁻¹' Set.univ= Set.univ:= by simp
  -- keep l at its exact restricted values; quiet unchanged
  rw [← Palette.at0 x0 H χ H' D E₀ V₀]; unfold foible Mosaic.showK; rw [he p]
  by_cases h:i∈Set.range A'; swap; · unfold shootK; rw [Progress.DirectedRecipe.blank _ _ h,Progress.DirectedRecipe.blank _ _ h]; simp
  obtain ⟨i,rfl⟩:=h; unfold A'; rw [stuffed]
  exact poly_paint H χ U H' D z hZ x0 g _ i u
include h hh
lemma quiet_lane (i : ℕ) (U' : Config G c) (y:α) :
    (HL y U' i).part Jm.quiet = ↑((XA).K i U'):= by
  let z' s:= (foible (brand M y) H χ Set.univ l 0 z H' D s U' i).part Jm.quiet
  have he:= Tendsto.comp (f:=fun s=> foible (brand M y) H χ Set.univ l 0 z H' D s U' i) (Poly.part_cont Jm.quiet|>.continuousAt.tendsto)
    ((Serif.station (brand M y) H χ Set.univ l 0 U h (Typeface.outputs H M x' y l 0 hh) z hZ H' D U').1 i)
  have hC: z'=fun _=>(((XA).K i U'):ℂ):=funext fun p=> quietFoible H χ U M y l H' D E₀ V₀ z hZ p i U'
  apply tendsto_nhds_unique (show Tendsto z' atTop (𝓝 ((HL y U' i).part Jm.quiet)) from he); rw [hC]; exact tendsto_const_nhds
omit h hh hZ U

-- general version later with variable z' t directly (mul controls and recover); constant
-- marker control here already allows *arbitrary Portrait* designs, not only linearized Stencils.
open Push Push.Corrected
private lemma authorized (S : Set ι) (p:BudgetPoint) (o: V'→Site c) (X: Support c)
    (q:Multiset ι) (h:∀ i∈q, Width.LocalCharge (G:=G) p o X (fun _=> z i)) :
    Width.LocalCharge (G:=G) p o X (fun _=> Verse.controls S z q) := by
  induction q using Multiset.induction_on with
  | empty => simp only [Verse.controls,Multiset.map_zero, Multiset.prod_zero]; 
             simpa only [Finset.prod_empty] using (Width.product_local (G:=G) (X:=X) (∅:Finset ℕ) (p:=p) (R:=Jm) (a:=o) (fun _=>0) (by simp))
  | cons i q ih => simp only [Verse.controls,Multiset.map_cons, Multiset.prod_cons]; split
                   next => exact (h i (Multiset.mem_cons_self ..)).mulCharges (ih fun j hj=> h j (Multiset.mem_cons_of_mem hj))
                   next => rw [one_mul]; exact ih fun j hj=> h j (Multiset.mem_cons_of_mem hj)
variable [Countable ι]
variable {origins : V'→ Site c}
local notation "K!"=> Flues.kettle H χ M x' l Set.univ 0 H' D E₀ V₀
local notation "Ψ"=> stuff (funnel H M x' H' D) (badge H M x' H' D)
local notation "ϕ"=> Flues.candle M x' S
variable (hc:∀ i, Width.LocalCharge (G:=G) P' origins (Flues.candle M x' S i) (fun _=> z i))
include ht hc U

def shaft : SameSlot.Group (Ψ) P' (XA).forced Jm origins α where
  val i y V := (K!).song Set.univ z y V i
  property i y := by
    let F:= K!; let a:= ((XA).forced (Ψ i)).support; let U' := Verse.controls Set.univ z (F.score i); let Q' := Flues.aligned H χ U M x' l Set.univ 0 H' D P' E₀ V₀ ht
    have hQ:=Q'.families y; let K i V:= ((F.glow y i V:ℝ):ℂ);
    refine ⟨fun s V=> congr_arg (· • U') (congr_arg ((↑):ℝ→ℂ) (hQ.sym i s V)), Measurable.smul (Complex.continuous_ofReal.measurable.comp (hQ.meas i)) measurable_const, ?_, ?_⟩
    · exact fun U V hx hp=> congr_arg (· • U') (congr_arg ((↑):ℝ→ℂ) (hQ.reads i U V hx hp))
    intro V j hj v hv; change (K i V • U').part j≠0 at hj; rw [Poly.part_smul] at hj
    refine (authorized (G:=G) z Set.univ P' origins a (F.score i) ?_).carry V j (right_ne_zero_of_mul hj) v hv
    intro t ht; exact (hc t).widen (Q'.invested i y t ht V (fun h=>left_ne_zero_of_mul hj (by unfold K;rw [h];norm_num)))
  permit i y V hp := (Flues.aligned H χ U M x' l Set.univ 0 H' D P' E₀ V₀ ht|>.families y).permit i V fun h=> hp (by unfold Yard.song; rw [show (K!).glow y i V=0 from h]; simp)

include h hh hp hZ
local notation "sh"=> shaft H χ U M x' l H' D P' ht E₀ V₀ z hc
local notation "fee0"=> (Real.exp ((-Q.mark L μ x)*(1/2:ℝ)) * gStep R.beta ^s)
lemma shaftPrice : (sh).Price gP P'.B a (fee0):=by
  obtain ⟨f,hf,hT,hF⟩:= (Flues.silk H χ U M x' l Set.univ 0 h hh H' D E₀ V₀ P' hp).wages
  let c i:= Verse.controls Set.univ z ((K!).score i); let z' i:= (↑(f i):ℂ) • Corrected.Width.up (c i); have he i: Poly.price gP (z' i) ≤ f i:=by
    unfold z'; rw [Poly.adapted,Complex.norm_real,Real.norm_of_nonneg (hf i), Width.shelter_same]; exact mul_le_of_le_one_right (hf i) (Serif.bought hZ _)
  refine ⟨z',?_,Labels.raise_prices _ _ (fun i=> Poly.nonnegative hZ.votes (z' i)) hT he⟩
  intro i t U' j; let v:= Verse.load Set.univ ((K!).score i); have hP := Width.shelter (c i) j
  have hv:=hP.1; have h:=f i; change ‖((↑((K!).glow t i U'):ℂ)•c i).part j‖ ≤ _ ∧ _; rw [Poly.part_smul]; dsimp only [z']; rw [Poly.part_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]; refine ⟨?_,?_⟩
  · rw [zero_mul,sub_zero,norm_mul]; by_cases he: v≤k; rw [Complex.norm_real]; exact mul_le_mul (hF i he t U') hv (norm_nonneg _) (hf i)
    simp only [show c i=0 from hZ.capacity _ (lt_of_not_ge he), Poly.part_nil, norm_zero,mul_zero]; exact mul_nonneg (hf _) ((norm_nonneg _).trans (Width.shelter 0 j).1)
  simp only [Complex.mul_im,Complex.ofReal_im,zero_mul,hP.2,mul_zero, add_zero]

omit h hh hp hZ in
lemma columnLane (t:α)(i:ℕ)(U':Config G c) : (sh).column t i U'= HL t U' i:= (Flues.echo H χ M x' t l Set.univ 0 z H' D E₀ V₀ U' i).symm

def layoutK : QuadraticLocal.Hard α P' (XA).forced (XA).K origins Jm := SameSlot.Group.hard sh
    (shaftPrice H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hc) h.price.visit.posts hZ.votes (fun i U' t => by
    rw [columnLane]; exact quiet_lane H χ U M x' l h hh H' D E₀ V₀ z hZ i U' t)
local notation "P0"=> layoutK H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hc
-- prior price, and exact on polynomial. No further support exponent loss over Lyric silk cost.
@[simp] lemma layoutK_hard (t:α)(i:ℕ)(U':Config G c) : (P0).hard t i U'=(HL t U' i) := columnLane _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
lemma layoutK_price : (P0).Paid gP P'.B a (fee0):= SameSlot.Group.pays sh (shaftPrice H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hc) h.price.visit.posts hZ.votes _ -- dots

-- conclusion including raw step with common vacuum. regular & unmask costs after this point.
lemma book_layout (t:α)(U':Config G c): Serif.book (brand M t) H χ Set.univ l 0 z H' D P' E₀ V₀ U'= Fusion.Attached.packet XA P' ((P0).hard t) U':=by
   ext1 i; unfold Serif.book Fusion.Attached.packet Merge.Photo.fronts; split; simp_rw [layoutK_hard]; rfl

variable (h₁:P'.order≤j)(h₂:P'.power≤J)(h₃:P'.supportExponent≤a)
variable [Fintype V']
include h₁ h₂ h₃
/-- The actual marked raw step in this common Hard representation. No separation uses in this
estimate and no price equivalence between shifted/differently reclosed vacua. -/
lemma carries (T':Tree.Forest S.ratio)(V':Config G c) (t:α):
    let v:= Serif.glyph (brand M t) H χ Set.univ l 0 z
    Summable (Fusion.Attached.packet XA P' ((P0).hard t) V') ∧
    S.push R.beta (Serif.TuneR (brand M t) Set.univ l 0 z S) V' =
       (Complex.ofReal (overhead (prism T x χ o.K V' T') R Q.table)) •
        (GridRenewal.Rain.cyclone (∑' i,v i V') * ∑' i,Fusion.Attached.packet XA P' ((P0).hard t) V' i):=by
    intro v'; rw [← book_layout]; exact (Serif.laws (brand M t) H χ Set.univ l 0 U h (Typeface.outputs H M x' t l 0 hh) z hZ H' D P' E₀ V₀ V' hp ht h₁ h₂ h₃ T').2

end YM.QuadraticLocal.Lanes
