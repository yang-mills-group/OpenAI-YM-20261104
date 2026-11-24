import YM.RegulatorIR.Primitives.Reed
import YM.RegulatorIR.Primitives.Ibis
import YM.RegulatorIR.Quadratic.Strength
import YM.RegulatorIR.Geometry.Forest

/-!
# Releasing arc assumptions: multi-step windings

No interdependence between top field insertions and choosing tape. Contraction
costs not in arc release. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Taping
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Geometry.Field Chart Gauge RG Orb Laplace Tree Forest Step Matrix Prim Binding.Last StopB Uniform Ledger Ledger.Sky
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W:Type}{M : W→ℕ}{n:Page M→Side}

abbrev Heir (n:Page M → Side)(G:Gauge):= Sky (fun _:Page M=>Foot G) (fun p=>Book G (n p))
variable (S:Heir n G)

-- only primitives and geometry. Does NOT provide RG_08 estimates. Include K-products on the given block choices; A Cover rec does not by itself imply block choices allowed. Uses only quadratic on cover and no orbits here.
structure Reel (S: Heir n G) where
 clock : Page M→ Binding.Scale
 steps : ∀ w:Flap M,StepData (n w.next) (n w.prev)
 phase : ∀ i:Page M,S.l i*(n i).val=S.P i.bindW
 even : ∀ i,Even (n i).val
 deep i : 4≤(n i).val
 realms i : S.maps i=Carto G _ _ (even i) (phase i)
 teeth w : (steps w).patch.Branches (steps w).kernel G
 forest : ∀ w, Tree.Forest (steps w).ratio
 landscape : ∀ w, Geometry.Field.Square (forest w)
 stem : Page M→ Layer (Foot G) (Foot G)
 apex : ∀ w, stem (Page.opening M w)= finer (moon (X:=G.ColorIndex))
 Dtr : Flap M→ Layer (Foot G) (Foot G)
 pulses : Flap M→ Layer (Foot G) (Foot G)
 meanF w : (S.frames w).driftL= Function.swap (hoses (Dtr w))
 bondF w : (S.frames w).line= petals (pulses w)
 moduli w : Bedload (S.maps w.prev) (S.maps w.next) (steps w).kernel.penalty (Quadratic.awake (steps w) (forest w)) (stem w.prev) (stem w.next) (finer (fringe (steps w))) (Dtr w) (pulses w)
 powers w :∃ T: Branchix→ Orders (KFoot G), Prim.Sphere (steps w) (forest w) (clock w.prev) T ∧ (S.frames w).addon=many T

namespace Reel
variable {S:Heir n G}(H : Reel S)

def stance (p:Page M): Matrix (Book G (n p)) (Book G (n p)) ℝ:= fmat (S.maps p) (S.maps p) (H.stem p)
def spot (p:Page M) := beneath (H.stance p)
lemma flagged (w):H.spot (Page.opening M w)=costO:=by rw [spot,stance,H.realms,H.apex]; exact sunrise ..
lemma steers (w) x : fmat (S.maps (Flap.next w)) (S.maps w.prev) (finer (fringe (H.steps w))) *ᵥ (paper G _ x)=paper G _ (rod G (H.steps w) x):= by
 rw [H.realms w.next,H.realms w.prev]
 exact steering (V:=H.teeth w) ..
lemma suited :∀ p, Vertex (H.spot p) ∧ (H.stance p).transpose=H.stance p:=by
 refine Page.proves ?_ ?_
 · intro w; rw [H.flagged]; refine ⟨fun x=>⟨costO_pos _,costO_null x (H.even _)⟩,?_⟩
   rw [stance,H.apex,H.realms]
   exact Quadratic.shines ..
 intro w hp; let F:=H.forest w; let s:=H.steps w; have hV : Vertex (H.spot w.prev):=hp.1; exact ⟨Quadratic.aged (H.moduli w).grid (H.steers w) hV (H.teeth w), StopB.elder_t (H.moduli w).grid⟩

-- dependent transport across Carto (Deck includes positions)
lemma growth (w:Flap M): Launch (H.steps w) (H.forest w) (H.clock w.prev) (S.frames w):=by
 obtain ⟨p,h,hp⟩:= H.powers w
 suffices hv: ∀ D: GridStep (S.maps w.prev) (S.maps w.next),D.addon=many p → Launch (H.steps w) (H.forest w) (H.clock w.prev) D from hv _ hp
 rw [H.realms w.prev,H.realms w.next]; intro D hd; exact Prim.debut _ _ _ (H.teeth w) _ _ _ _ D h hd
lemma near (w:Flap M): Nonempty (FitsO (S.frames w) (H.steps w) (H.forest w) (H.clock w.prev) (H.spot w.prev) (H.spot w.next)):= by
 have ht:= H.growth w;exact boot _ (H.moduli w) (H.bondF w) (H.meanF w) (H.suited _).1 (H.steers w) (H.even _) (H.even _) (H.landscape w) (H.teeth w) ht

def docket : Binding.Docket S:= {
 clock:= H.clock,rates:=H.spot, order:=H.steps, connected:=H.phase, even:=H.even, large:=H.deep, compatible:=H.realms, bushes:=H.forest, landscape:=H.landscape, legs:=H.near,top:=H.flagged,teeth:=H.teeth }

def vapors (i: Page M): Layer (Book G (n i)) (Book G (n i)):=axis (H.suited i).1 (H.suited i).2 (H.even i)

def feeMarg : Margins (fun w=> Book G (n w)):= { endK:=fun w=> H.vapors (Page.finallyW M w),haar:=fun w=> charter G (n (Page.finallyW M w)) }
lemma learned : aliases H.docket H.feeMarg:= fun _=>lens (H.suited _).1 (H.suited _).2 _

variable (T:S.Accounts)
-- top docket arc

def Follows : Prop:=∀ w,let i:=Page.opening M w; ∃ V:Face ℤ → Orders (Foot G), Plane (H.clock i) G V ∧ T.bulk i=many V ∧ T.orb i= fun e r=>(S.maps i).deckSum (T.bulk i e r)
lemma accorded (V:H.Follows T) (w): let i:=Page.opening M w; (∀ x,flavor 2 (tint G (n i) x) (T.orb i)= logread (priceMap (startO (H.clock i))) (0,1,x)) ∧ gradedSymmetric (T.orb i):=by
 intro i; obtain ⟨v,h,hv,hy⟩:=V w; change T.orb i=fun e r=>(S.maps i).deckSum (T.bulk i e r) at hy; change T.bulk i= _ at hv; rw [hy,H.realms,hv]; exact ⟨log_eye _ (H.even _) (H.phase _) h,(ark _ (H.even _) (H.phase _) h).printed⟩
end Reel
end YM.RegulatorIR.Taping
