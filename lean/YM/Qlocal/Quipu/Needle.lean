import YM.Qlocal.Quipu.Albums
import YM.Qlocal.Quipu.Wall
/-!
# Tilt interpretation of each rooted ALL positions log coloring. Evaluates in ℂ
 marker algebra (also handy for MULTILINEAR pol budget). Spectator fields
 ζ are real. coefficient extraction before sparse ambient f. Preserve stencil
 shifts by construction. Further angular receipts charge.P.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c f:Side} {S:StepData c f}{d t a v u C:ℝ}{R:Census V}
open Album
open Primitives.TwoWave
variable [Fintype V]
abbrev Places (s:Senses R)(n:Side):=↥(essence s)→ Site n
protected noncomputable def fill (s:Senses R)(a:Places s c)(v:V): Site c:= if h:v∈ essence s then a ⟨v,h⟩ else 0
def selected (s:Senses R)(o:V→Site c): Places s c:= fun i=> o i
variable (o:V→Site c) {s:Senses R} (Q:Places s c)
lemma filled_here (i:V)(hi:i∈ essence s) : Sonnet.fill s (selected s o) i=o i:= dif_pos hi
local notation "X"=> Site c × V
local notation "s₀"=> essence s
set_option quotPrecheck false
noncomputable def viewed (R:Census V)(o:V→Site c)(i: Leaf c V): Poly R:= if i.1 = o i.2 then Poly.send (R.fire i.2) 1 else 0
local notation "K"=> viewed R o
noncomputable def placard (a:Places s c) (p: (Site c × V)→ℝ):ℝ:= ∏ i:↥(essence s), p (a i,i.val)
open Turbin
lemma priced_tokens (Y:Leaf c V→ Poly R): wall Y (placard Q)=∏ i:↥(essence s), Y (Q i,i.val):= by
 let d (i:↥(essence s)): (Leaf c V→ℝ)→ℝ := fun x=> x (Q i,i.val)
 rw [show placard Q= ∏ i,d i from funext fun p=>(show (∏ i,d i) p= _ from Finset.prod_apply p univ d).symm]; rw [Turbin.products]; · exact Finset.prod_congr rfl fun i _=> sky_x ..
 intro i _; exact Plausible.line (LinearMap.proj (φ:=fun _:Leaf c V=>ℝ) (Q i,i.val))
open Extra.Trajectories
lemma owns : wall K (placard Q) = if selected s o=Q then Poly.send s.val 1 else 0:= by
 rw [priced_tokens]; let g (i:↥s₀):= R.fire i; split
 next he =>
    rw [← he]; unfold viewed selected; simp_rw [if_true];
    let h : Finset.biUnion univ (fun i=> (g i).val)=s₀ := by ext1 i; simp [g,Census.fire]
    have hh: Fits g univ:= by
       refine ⟨fun i hi j hj he=> ?_, h.symm ▸ s.val.property⟩; change Disjoint ({↑i}:Finset V) {↑j}; exact Finset.disjoint_singleton.mpr (fun H=> he (Subtype.ext H))
    rw [tagged_prod g _ hh, show unionTag g _ hh=s.val from Subtype.ext h,Finset.prod_const_one]
 next he=>
    obtain ⟨i,hi⟩:= Function.ne_iff.mp he
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi.symm) -- maybe `hi.symm` subtype decidable Eq defeq
local notation "Y"=> Poly R
lemma product_rank : AllOrder.Fire.Rank (Leaf c V→ℝ) (essence s).card (placard Q):= by
 let f i := Q i; let x'(i:↥s₀):= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Leaf c V=>ℝ) ((Q i),i.val); have ht (v: Finset ↥s₀): AllOrder.Fire.Rank (Leaf c V→ℝ) v.card fun p=> ∏ i∈v,x' i p:= by
    induction v using Finset.induction_on with
    | empty=> simp_rw [Finset.card_empty, Finset.prod_empty]; exact AllOrder.Fire.Rank.nil _ _
    | insert i s hi ih=> simp_rw [card_insert_of_notMem hi,Finset.prod_insert hi]; exact AllOrder.Fire.Rank.dot _ _ ih
 exact (show Fintype.card (↥(essence s))=(essence s).card from Fintype.card_coe _ ) ▸ (by have hp:= ht univ; simp_rw [card_univ] at hp; exact hp)
-- lane portal `v` any placement.W.B. support matches.Carrier.
end YM.Qlocal.Quipu.Sonnet
