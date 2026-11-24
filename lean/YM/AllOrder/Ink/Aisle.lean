import YM.AllOrder.Ink.Plant
import Mathlib.Data.List.InsertIdx
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Field
open GaussianScore
-- mark slips not multiset. observe one incidence by list index.
abbrev LeafIdx {A:Type*}(S: Slip A):= Fin S.length
abbrev eraseT {A:Type*}(S: Slip A)(i:LeafIdx S):= List.eraseIdx S i.val
abbrev knot {A:Type*}(S: Slip A)(i:LeafIdx S):= S.get i
omit [Fintype α] in
lemma ending (S:Slip (Point α))(p:LeafIdx S): meter (eraseT S p)+size (knot S p).1 = meter S:= by
 induction S with
 | nil=>exact Fin.elim0 p
 | cons a S ih=>
    refine Fin.cases ?_ ?_ p
    · change meter S+size a.1= size a.1+meter S; rw [add_comm]
    intro i; change (size a.1 + meter (eraseT S i))+size (knot S i).1 = size a.1+meter S; rw [add_assoc, ih]
lemma look (z:Site n)(v:Point α) : Rank (rule α n) 1 (fun x=> x (stood z v)):= Rank.line (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Leaf n α=>ℝ) (stood z v))
lemma inked (z:Site n) (i:Leaf n α)(S: Slip (Point α)): diff' (spot i) (invoice z S)=∑ p:LeafIdx S,(if stood z (knot S p)=i then invoice z (eraseT S p) else 0):= by
 induction S with
 | nil=> letI:IsEmpty (LeafIdx ([]:Slip (Point α))) := inferInstanceAs (IsEmpty (Fin 0)); rw [Finset.sum_of_isEmpty]; exact dift ..
 | cons v S ih=>
    rw [invoice_cons,mults (look z _).read (ticket z S).2.1.read, ih]; erw [Fin.sum_univ_succ]
    let V:= stood z v; let L: rule α n→L[ℝ] ℝ:= ContinuousLinearMap.proj (R:=ℝ) V; let B:= invoice z S
    change diff' (spot i) L*B + (L:rule α n→ℝ)*_ = (if V=i then B else 0)+ _; rw [Finset.mul_sum]; refine congr_arg₂ (·+·) ?_ (Finset.sum_congr rfl fun p _=>?_)
    · ext1 x; simp only [diff',Pi.mul_apply]; rw [ContinuousLinearMap.fderiv]; by_cases h:V=i <;> simp only [h,if_true,if_false,Pi.zero_apply] <;> change spot i V * _=_; · rw [h]; simp [spot]
      simp [spot,h] -- rw fails etc.
    change (L:rule α n→ℝ)*(if stood z (knot S p)=i then invoice z (eraseT S p) else 0)=(if stood z (knot S p)=i then invoice z (v::eraseT S p) else 0); split; exact (invoice_cons ..).symm; exact mul_zero _

def plus (S:Point α)(z:Cover) : Point α:= (z+S.1,S.2)
def along (v:Cover) (P:Slip (Point α)) : Slip (Point α) := P.map fun i=> plus i v
omit [Fintype α] in
lemma lifted_cost (P: Slip (Point α))(v:Cover) : meter (along v P) ≤ P.length*size v+meter P:=by induction P with
 | nil=> simp [meter,along]
 | cons x P ih=> simpa [meter,along,Nat.add_mul,plus,add_left_comm,add_assoc,add_comm] using (Nat.add_le_add (size_add v x.1) ih) -- simp
omit [Fintype α] in
lemma bend (z:Site n)(v:Cover)(i:Point α) : stood z (plus i v) = stood (z+wrap n v) i:= Prod.ext (by unfold plus stood; dsimp only; rw [map_add,add_assoc]) rfl
omit [Fintype α] in
lemma lifted (z:Site n)(v:Cover)(S:Slip (Point α)): invoice z (along v S)=invoice (z+wrap n v) S:= by induction S with
 | nil=> rfl
 | cons i S ih=> change invoice z (plus i v::along v S)=_; rw [invoice_cons,invoice_cons, bend,ih]
end Field
end YM.AllOrder.Ink
