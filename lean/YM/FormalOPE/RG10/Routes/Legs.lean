import YM.FormalOPE.RG10.Join.Heat
import YM.FormalOPE.RG10.Routes.Prices

/-! # Split Gaussian and still-unevaluated legs, for all-order primitive pieces -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open MvPolynomial Finset Marker Extra.Trajectories Joins Joins.Gauss Function
open Multi (parts shards)
open Primitives.GCC (size Growth)
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I J B : Type} [Fintype J]

abbrev Index (I B:Type) := Letters (I ⊕ B)
variable (c : Index I B)
def fine : Letters I := c.comapDomain Sum.inl Sum.inl_injective.injOn
def coarse : Letters B := c.comapDomain Sum.inr Sum.inr_injective.injOn
lemma sound : c=(fine c).sumElim (coarse c) := (Finsupp.comapDomain_sumElim_comapDomain c).symm
lemma fine_mem (a : I) : a ∈ (fine c).support ↔ Sum.inl a ∈ c.support := by simp [fine,Finsupp.mem_support_iff]
lemma coarse_mem (a : B) : a ∈ (coarse c).support ↔ Sum.inr a ∈ c.support := by simp [coarse,Finsupp.mem_support_iff]

def glyph (i : Letters I) : Packet I := monomial i 1
lemma glyph_eval_add (x : I→ℂ) (i j : Letters I) : aeval x (glyph (i+j)) = aeval x (glyph i)*aeval x (glyph j) := by
  rw [← map_mul]; congr 1; unfold glyph; rw [monomial_mul,one_mul]
lemma glyph_prod {Z : Type*} (s:Finset Z) (x:I→ℂ) (v: Z → Letters I) : aeval x (glyph (∑ i∈s,v i)) = ∏ i∈s, aeval x (glyph (v i)) := by
  induction s using Finset.induction_on with
  | empty => simp [glyph]
  | @insert i s hi h => rw [sum_insert hi,glyph_eval_add,h,prod_insert hi]

variable (q : I → Row J)

/-- One fluctuation port's eligibility. -/
def reading (a:I) : hall J := by
  let Q := q a; let x : Unit × Row J → ℂ := fun r => ↑(crossed Q r.2)
  refine ⟨x,show admissible x from ⟨Complex.continuous_ofReal.comp (Primitives.GCC.crossed_cont Q),?_⟩⟩
  dsimp only [x];
  obtain ⟨j,k,h,r⟩ := Primitives.GCC.Growth.lines (s:=Set.univ) (q:=fun _:Unit=>Q) (M:=squares Q) (Primitives.GCC.squares_nn _) (fun _ _=>le_rfl)
  refine ⟨k,j,h,fun t=>?_⟩; rw [Complex.norm_real]; change ‖crossed Q t‖ ≤ k * size t ^ j; simpa using r () (Set.mem_univ _) t

def leaking : Packet I →ₐ[ℂ] hall J := aeval (reading q)

def alongFine (t : Row J) : I→ℂ := fun i => ↑(crossed (q i) t)
lemma leaking_apply (p : Packet I) (x) : (leaking q p).val x = aeval (alongFine q x.2) p := by
  let U : Packet I →ₐ[ℂ] ℂ := (Pi.evalAlgHom ℂ (fun _ : Unit × Row J => ℂ) x).comp ((hall J).val.comp (leaking q))
  have h : U=aeval (alongFine q x.2) := by ext u; change (leaking q (X u)).val x=_; rw [leaking,aeval_X,aeval_X]; rfl
  change U p = _; rw [h]
variable (y : B→ℂ)
/-- A whole graph *node* polynomial under one common Gaussian argument, at the stated projection,
no global tag.
-/
def study : Packet (I⊕B) →ₐ[ℂ] hall J := aeval (Sum.elim (reading q) (fun x => algebraMap ℂ (hall J) (y x)))
lemma study_apply (p : Packet (I⊕B)) (x) : (study q y p).val x= aeval (Sum.elim (alongFine q x.2) y) p := by
  let U : Packet (I⊕B) →ₐ[ℂ] ℂ := (Pi.evalAlgHom ℂ (fun _ : Unit × Row J => ℂ) x).comp ((hall J).val.comp (study q y))
  have h : U=aeval (Sum.elim (alongFine q x.2) y) := by ext (u|u); all_goals change (study q y (X _)).val x=_; rw [study,aeval_X,aeval_X]; rfl
  change U p=_; rw [h]

lemma rolled (b : ℂ) : study q y (monomial c b) = (aeval y (monomial (coarse c) b : Packet B)) • (leaking q (glyph (fine c))) := by
  ext x; rw [study_apply]; change _=(aeval y (monomial (coarse c) b : Packet B)) * ((leaking q (glyph (fine c))).val x); rw [leaking_apply];
  unfold glyph; simp only [aeval_monomial]; nth_rw 1 [sound c]
  rw [Finsupp.prod_sumElim]; simp only [RingHom.algebraMap_toAlgebra, RingHom.id_apply, one_mul];
  change b*(_*_)=(b*(coarse c).prod fun i n => y i^n) * (fine c).prod fun i n=>_
  simp only [Function.comp_def,Sum.elim_inl, Sum.elim_inr]; ring
end YM.FormalOPE.RG10.Route
