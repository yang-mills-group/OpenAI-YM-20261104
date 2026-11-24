import YM.LocalLTE.Ballot.Permit
import YM.LocalLTE.River.Solo
/-!
## A capacity with genuine receipts for inherited PT certificates

At *actual budget point*, inside the slot. The analytic condition has to pay for
full post-projection. rank ζ may be bought higher on each stage. The leading
budget included to give direct absolute convergence of predicted canonical leads,
even for infinitely spread readers. For a named job we require conservation of
support even where amplitude is zero; this has implications even for what kind of
normalizations of the entries are possible. Canonical at root zero; orientations
and placements charged when applied.

See also previous stencil pilots. "Patrons" below are AUTHORIZATIONS; separate
implementation checks for how these are to be generated. These are just pieces
of the engine.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.River
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n κ:Side}{p:BudgetPoint}{d:ℕ}{F:Labels.Frame G d}{A:Hol G}{D:SectionData F}{R:Rep G n}{k v a u u' s t e x y z:ℝ}{m m' ℓ j:ℕ}{i:Site n}
local notation "Xp"=> Config G n→ℂ
open Next.Foundations Push.AbsoluteSums Animals -- neighbors
variable {L:Support n} {g f:Config G n →ℂ}
structure Canvas (D:SectionData F)(k:ℝ)(ℓ m:ℕ)(p:BudgetPoint)(L:Support n)(f:Config G n→ℂ)(u:ℝ):Prop where
    value : p.supBounds 0 L f u
    analytic : f ≠ 0 → L⊆ neighbors ℓ 0 ∧
       ∃ g:Config G n → ℂ, p.Regular L g ∧ p.supBounds 0 L g u ∧ (∃ c:F.Coeff, F.coeffSize c ≤ u ∧ f=g+presented D 0 p.threshold c)∧ ∃ j≤ℓ,∃ Z:Grove (0:Site n),∀ b:Bool,Replicated Z j k (m+1) (Port.scaleQ b ∘ g)
lemma Canvas.earn (h:Canvas D k ℓ m p L f u):0 ≤ u:=h.value.1
lemma Canvas.quiet (hx:0 ≤ x):Canvas D k ℓ m p L 0 x:=⟨bound_weaken (bound_const (o:=0) (0:ℂ)) (by simpa using hx),fun h=>(h rfl).elim⟩
lemma Canvas.raise (h:Canvas D k ℓ m p L f u)(hp:u ≤ u')(hv: m≤j)(he:ℓ ≤ m') : Canvas D k m' j p L f u':=by
    refine ⟨bound_weaken h.value hp, fun hf=>?_⟩; obtain ⟨hκ,g,hp',hr,⟨c,hV,hQ⟩,b,hB,Z,hZ⟩:= h.analytic hf -- nested
    refine ⟨fun i hi=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp (hκ hi)).trans he),g,hp', bound_weaken hr hp,⟨c,hV.trans hp,hQ⟩,b,hB.trans he,Z, fun i=> Price.rp_raise Z (hZ i) (by omega)⟩

open Planned.GuardedAtom
structure Patrons (D:SectionData F)(k:ℝ)(ℓ m:ℕ)(p:BudgetPoint)(P:Coefficient F n)(x:ℝ):Prop where
    principal:F.coeffSize P.x ≤ x
    regular:∃ q:ℕ→ℝ, SumBudget (fun i=> p.mass (P.support i) (q i)) x ∧ ∀ i, Canvas D k ℓ m p (P.support i) (P.regular i) (q i)
    forced:P.forced=0

variable {P Q:Coefficient F n}
lemma Patrons.cost (h:Patrons D k ℓ m p P x):0≤x:=(Work.G08.size_nonneg ..).trans h.principal
lemma Patrons.bill (h:Patrons D k ℓ m R.p Q v)(hp:0<s):Tab Q 0 R s v 0:=by
    refine ⟨hp,h.cost, le_rfl, ?_,?_⟩
    · obtain ⟨q,hx,hq⟩:= h.regular; exact ⟨q,hx,fun i=> (hq i).value⟩
    rw [h.forced,mul_zero]; exact ⟨(fun i=> 0), by simp [BudgetPoint.mass, SumBudget]⟩
lemma Patrons.raise (h:Patrons D k ℓ m p P x)(hp:x≤x+a)(he:ℓ≤ m')(hv:m≤j): Patrons D k m' j p P (x+a):=by
    refine ⟨h.principal.trans hp,?_,h.forced⟩; obtain ⟨q,hq,ht⟩:=h.regular; exact ⟨_,⟨hq.1,hq.2.1,hq.2.2.trans hp⟩,fun i=> (ht i).raise (le_refl _) hv he⟩
lemma Patrons.priced (h:Patrons D k ℓ m p P x)(hp:x≤y):Patrons D k ℓ m p P y:=by convert! h.raise (a:=y-x) (by linarith) (le_refl _) (le_refl _) using 1; abel
lemma tabWeaken (h:Tab P i R k x y)(hp:x≤u)(hb:y ≤ v):Tab P i R k u v:=by
    refine ⟨h.divisor,h.first.trans hp, h.second.trans hb, ?_,?_⟩; obtain ⟨q,hq,ht⟩:=h.regular; exact ⟨q,⟨hq.1,hq.2.1,hq.2.2.trans hp⟩,ht⟩
    obtain ⟨q,hq,ht⟩:=h.forced; exact ⟨q,⟨hq.1,hq.2.1,hq.2.2.trans (mul_le_mul_of_nonneg_left hb h.divisor.le)⟩,ht⟩
structure Exhibition (D:SectionData F) (k:ℝ)(ℓ m:ℕ)(A:Hol G)(R:Rep G n)(P Q:Coefficient F n)(κ v e:ℝ) : Prop where
    stock: Patrons D k ℓ m R.p Q v
    format: Q.Format 0 A R
    layout:P.support=Q.support
    trade:(Vinca.decrement P Q).Format 0 A R
    fee:Tab (Vinca.decrement P Q) 0 R κ e e
    canon:F.coeffSize ((Vinca.decrement P Q).x) ≤ e

lemma Exhibition.large (h:Exhibition D k ℓ m A R P Q s v e) (hv:v≤x)(hp:e≤y)(hκ:m≤j)(hZ:ℓ≤ m'):Exhibition D k m' j A R P Q s x y:=by
    refine ⟨?_,h.format,h.layout,h.trade,tabWeaken h.fee hp hp,h.canon.trans hp⟩; convert (h.stock.priced hv).raise (a:=0) (by simp) hZ hκ using 1; rw [add_zero]
lemma Exhibition.pledge (h:Exhibition D k ℓ m A R P Q s v e) (hv:v≤x)(hp:e≤y): Exhibition D k ℓ m A R P Q s x y:=h.large hv hp le_rfl le_rfl
-- every row. use ChartPlm for Hats. lead estimation recurrence.
lemma Exhibition.price (h:Exhibition D k ℓ m A R P Q s v e): F.coeffSize P.x ≤ v+e:=by
    rw [show P.x=Q.x+ (decrement P Q).x from by change P.x= Q.x +(P.x-Q.x); abel]
    exact (Size.add ..).trans (add_le_add h.stock.principal h.canon)
variable {B:BudgetPoint}
end YM.LocalLTE.River
