import YM.QuadraticLocal.Lane
import YM.QuadraticLocal.Rough.Emit
/-!
 # Uniform pressure K reclosure refund at stronger setup. all marks
 Uses the very same estimator from Semester.Lanes. Last valuation uses
 hpV; hT required even for exact call.Ar. alpha. Earn MASK moves beyond
 these witnesses on Portal.Out.We.Care.Record.Actor.Author`. Need enough Bool
 frames.ShapeConsumer.Carr.Reg.K.Tile.`
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
variable (z:ι→Marker.Poly Jm) {gP:V'→ℝ} {kZ:ℕ}(hZ : Chorus Jm gP Set.univ z kZ)

local notation "XA" => Refrain.read H' D χ E₀ V₀
local notation "HL" => fun y:α => Lane (brand M y) H χ Set.univ l 0 z H' D


variable (hT : Glit.LeasePlot (brand M x') H l Y τ)
local notation "TZ"=> ( Set.univ : Set ι )
lemma traversed (hT : Glit.LeasePlot (brand M x') H l Y τ) : Glit.LeasePlot (brand M y) H l Y τ:= by obtain ⟨I,K,w,hF⟩:=hT.cost; exact ⟨I,K, Typeface.outputs H M x' y l 0 w,hF⟩
include hT h hh hZ U
lemma quietLane (i : ℕ) (U' : Config G c) (y:α) :
    (HL y U' i).part Jm.quiet = ↑((XA).K i U'):= by
  let z' s:= (foible (brand M y) H χ Set.univ l 0 z H' D s U' i).part Jm.quiet
  have he:= Tendsto.comp (f:=fun s=> foible (brand M y) H χ Set.univ l 0 z H' D s U' i) (Poly.part_cont Jm.quiet|>.continuousAt.tendsto)
    ((Serif.stationFull (brand M y) H χ l 0 U h (Typeface.outputs H M x' y l 0 hh) z hZ H' D (traversed H M x' y l hT) U').1 i)
  have hC: z'=fun _=>(((XA).K i U'):ℂ):=funext fun p=> quietFoible H χ U M y l H' D E₀ V₀ z hZ p i U'
  apply tendsto_nhds_unique (show Tendsto z' atTop (𝓝 ((HL y U' i).part Jm.quiet)) from he); rw [hC]; exact tendsto_const_nhds
variable [Countable ι]
variable {origins : V'→ Site c}
local notation "K!"=> Flues.kettle H χ M x' l Set.univ 0 H' D E₀ V₀
local notation "Ψ"=> stuff (funnel H M x' H' D) (badge H M x' H' D)
local notation "ϕ"=> Flues.candle M x' S
open Push Push.Corrected
variable (hc:∀ i, Width.LocalCharge (G:=G) P' origins (Flues.candle M x' S i) (fun _=> z i))

-- uniform `Flues.silk` version
omit h hZ hh hT U in
include χ in
lemma bank (i:Muse.Flak Vx H): Mosaic.Bank Vx H l i.1 i.2=Mosaic.Bank Vy H l i.1 i.2 := by
    have hF(p:H.Chapter)(l:ι→ℝ)(w:Mosaic.Stone Vx H p) : Mosaic.pay Vx H l p w=Mosaic.pay Vy H l p w:=by cases p <;>rfl
    unfold Mosaic.Bank; split; exact Finset.prod_congr rfl fun a _=> congr_arg (·/_) (Finset.prod_congr rfl fun j _=> hF _ _ _); rfl


local notation "topF"=> (funnel H M x' H' D)
omit hZ hh in
lemma silkAll (y:ℕ) (P':BudgetPoint)(hx:P'.B=radiusB x): Yard.Pays K! TZ y P'.B a (Real.exp ((-Q.mark L μ x)*(1/2:ℝ)) * (gStep R.beta)^s) :=by
 let A':= Elbow H M x'; let d:A'↪Flak Vx H:= Embedding.sigmaMap (Embedding.subtype _) fun i=> Embedding.refl (Serif.KEntry Vx H i)
 let f (z:Flak Vx H):= Mosaic.Bank Vx H l z.1 z.2; have hw (i: Flak Vx H):= Glit.security Vx H χ l U h hT i (1:Config G c); have hp (i:Flak Vx H):0≤ f i:=( norm_nonneg _ ).trans (hw i); let ht' := Glit.weather Vx H χ l U h hT
 let b':=fun i:A'=> f (d i); let s':=stuff topF b'; have he i:0 ≤ s' i:=Progress.DirectedRecipe.Rack.positive topF b' (fun _=>hp _) i; refine ⟨s',he,fun v=> transfer_budget topF (fun j=> ?_) (fun j hj=> ?_) (budget_pull d (d.injective) (ht' v)),fun j hj a Ux=>?_⟩
 · unfold Yard.plane kettle s'; dsimp only; simp_rw [stuffed,hx]; rw [show ((XA).forced (badge _ _ _ _ _ j)).support=_ from (Refrain.admitted H' D j.fst).1]; rfl
 · split; next=> unfold s'; rw [Progress.DirectedRecipe.blank _ _ hj,zero_mul]
   next=>exact rfl
 by_cases hi:j ∈ Set.range topF
 swap; · rw [show (K!).glow a j=0 from by unfold kettle; dsimp only; rw [Progress.DirectedRecipe.blank _ _ hi]]; simpa using he j
 obtain ⟨i,rfl⟩:=hi; unfold s' b'; rw [stuffed]; unfold f; rw [Lanes.bank H χ M x' a l]; unfold kettle; dsimp only; rw [stuffed]; change ‖( Mosaic.parade (brand M a) H χ (d i).1 (d i).2).emit (sits TZ l 0) Ux‖≤ _; rw [show sits TZ l 0=l from (by ext; simp [sits,Verse.marked])]; exact Glit.security (brand M a) H χ l U h (traversed H M x' a l hT) (d i) Ux
include h hh hp hZ hc ht
local notation "sh"=> shaft H χ U M x' l H' D P' ht E₀ V₀ z hc
local notation "fee0"=> (Real.exp ((-Q.mark L μ x)*(1/2:ℝ)) * gStep R.beta ^s)
lemma shaftValue : (sh).Price gP P'.B a (fee0):=by
  obtain ⟨f,hf,hT,hF⟩:= (Lanes.silkAll H χ U M x' l h H' D E₀ V₀ hT kZ P' hp).wages
  let c i:= Verse.controls Set.univ z ((K!).score i); let z' i:= (↑(f i):ℂ) • Corrected.Width.up (c i); have he i: Poly.price gP (z' i) ≤ f i:=by
    unfold z'; rw [Poly.adapted,Complex.norm_real,Real.norm_of_nonneg (hf i), Width.shelter_same]; exact mul_le_of_le_one_right (hf i) (Serif.bought hZ _)
  refine ⟨z',?_,Labels.raise_prices _ _ (fun i=> Poly.nonnegative hZ.votes (z' i)) hT he⟩
  intro i t U' j; let v:= Verse.load Set.univ ((K!).score i); have hP := Width.shelter (c i) j
  have hv:=hP.1; have h:=f i; change ‖((↑((K!).glow t i U'):ℂ)•c i).part j‖ ≤ _ ∧ _; rw [Poly.part_smul]; dsimp only [z']; rw [Poly.part_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im]; refine ⟨?_,?_⟩
  · rw [zero_mul,sub_zero,norm_mul]; by_cases he: v≤kZ; rw [Complex.norm_real]; exact mul_le_mul (hF i he t U') hv (norm_nonneg _) (hf i)
    simp only [show c i=0 from hZ.capacity _ (lt_of_not_ge he), Poly.part_nil, norm_zero,mul_zero]; exact mul_nonneg (hf _) ((norm_nonneg _).trans (Width.shelter 0 j).1)
  simp only [Complex.mul_im,Complex.ofReal_im,zero_mul,hP.2,mul_zero, add_zero]

def layoutGlobal : QuadraticLocal.Hard α P' (XA).forced (XA).K origins Jm := SameSlot.Group.hard sh
    (shaftValue H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hT hc) h.price.visit.posts hZ.votes (fun i U' t => by
    rw [columnLane]; exact quietLane H χ U M x' l h hh H' D E₀ V₀ z hZ hT i U' t)
local notation "P0"=> layoutGlobal H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hT hc
-- prior price, and exact on polynomial. No further support exponent loss over Lyric silk cost.
@[simp] lemma layoutGlobal_hard (t:α)(i:ℕ)(U':Config G c) : (P0).hard t i U'=(HL t U' i) := columnLane _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
lemma layoutGlobal_price : (P0).Paid gP P'.B a (fee0):= SameSlot.Group.pays sh (shaftValue H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hT hc) h.price.visit.posts hZ.votes _ -- dots

-- conclusion including raw step with common vacuum. regular & unmask costs after this point.
lemma bookGlobal (t:α)(U':Config G c): Serif.book (brand M t) H χ Set.univ l 0 z H' D P' E₀ V₀ U'= Fusion.Attached.packet XA P' ((P0).hard t) U':=by
   ext1 i; unfold Serif.book Fusion.Attached.packet Merge.Photo.fronts; split; simp_rw [layoutGlobal_hard]; rfl

variable (h₁:P'.order≤j)(h₂:P'.power≤J)(h₃:P'.supportExponent≤a)
variable [Fintype V']
include h₁ h₂ h₃
/-- The actual marked raw step in this common Hard representation. No separation uses in this
estimate and no price equivalence between shifted/differently reclosed vacua. -/
lemma grand {φ:ℝ}(hpF:1 ≤ φ)(hΩ:Motto (brand M x') (Lyric.mulScale ( Y*φ ) l) 0 H τ K Y I) (T':Tree.Forest S.ratio)(V':Config G c) (t:α):
    let v:= Serif.glyph (brand M t) H χ Set.univ l 0 z
    Summable (Fusion.Attached.packet XA P' ((P0).hard t) V') ∧
    S.push R.beta (Serif.TuneR (brand M t) Set.univ l 0 z S) V' =
       (Complex.ofReal (overhead (prism T x χ o.K V' T') R Q.table)) •
        (GridRenewal.Rain.cyclone (∑' i,v i V') * ∑' i,Fusion.Attached.packet XA P' ((P0).hard t) V' i):=by
    intro v'; rw [← bookGlobal]; exact (Serif.emitted (brand M t) H χ l 0 U h (Typeface.outputs H M x' t l 0 hh) z hZ H' D P' E₀ V₀ hpF ( Typeface.outputs H M x' t _ 0 hΩ ) (traversed H M x' t l hT) V' hp ht h₁ h₂ h₃ T').2


end YM.QuadraticLocal.Lanes
