import YM.Integration.WilsonOriginalOccupiedTap
import Mathlib.Algebra.Polynomial.BigOperators

/-! Each original compatible packet is a polynomial in the one hard amplitude.
    Its degree at a face is bounded by that face's actual number of occupied names. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedDegree
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached Polynomial
open scoped BigOperators Classical
variable {V:Type} [DecidableEq V] {R:Census V}

def Rendered (F:ℂ→Poly R):Prop :=∀s:R.Mode,∃p:Polynomial ℂ,p.natDegree ≤ s.val.card ∧ ∀z,p.eval z=(F z).part s

theorem constant (a:Poly R):Rendered (fun _=>a):=by
  intro s
  refine ⟨C (a.part s),?_,by simp⟩
  simp

theorem product {F H:ℂ→Poly R} (f:Rendered F)(h:Rendered H):Rendered (fun z=>F z * H z):=by
  intro s
  choose A a ea using f
  choose B b eb using h
  let summand (i j:R.Mode):Polynomial ℂ:=if Poly.merges i j s then A i * B j else 0
  refine ⟨∑i,∑j,summand i j,?_,?_⟩
  · apply natDegree_sum_le_of_forall_le
    intro i _
    apply natDegree_sum_le_of_forall_le
    intro j _
    unfold summand
    split
    next joined =>
      have sizes:i.val.card+j.val.card=s.val.card:=by rw [←card_union_of_disjoint joined.1,joined.2]
      exact natDegree_mul_le.trans ((Nat.add_le_add (a i) (b j)).trans_eq sizes)
    next => simp
  · intro z
    rw [Poly.part_mul,Polynomial.eval_finsetSum]
    apply sum_congr rfl
    intro i _
    rw [Polynomial.eval_finsetSum]
    apply sum_congr rfl
    intro j _
    simp only [summand]
    split <;> simp [ea,eb]

theorem finite {ι:Type} (S:Finset ι)(f:ι→ℂ→Poly R)(paid:∀i,Rendered (f i)):
    Rendered (fun z=>∏i∈S,f i z):=by
  induction S using Finset.induction_on with
  | empty =>simpa only [prod_empty] using (constant (1:Poly R))
  | @insert i S fresh ih =>
    simpa only [prod_insert fresh] using (product (paid i) ih)

theorem affine (a:Poly R):Rendered (fun z=>WilsonOriginalOccupiedTap.paint z a):=by
  intro s
  by_cases quiet:s=R.quiet
  · refine ⟨C (a.part s),by simp,?_⟩
    intro z
    change _=WilsonOriginalOccupiedTap.amount z s*a.part s
    simp [WilsonOriginalOccupiedTap.amount,quiet]
  · refine ⟨monomial 1 (a.part s),?_,?_⟩
    · exact (natDegree_monomial_le _).trans (card_pos.mpr (nonempty_iff_ne_empty.mpr fun he=>quiet (Subtype.ext he)))
    · intro z
      change _=WilsonOriginalOccupiedTap.amount z s*a.part s
      simp [WilsonOriginalOccupiedTap.amount,quiet,mul_comm]

variable {G:Gauge} {n:Side} {P:Rep G n} {o:V→Site n} {X I:Type}

theorem packet (A:Gallery X I o P R) (x:X) (U:Config G n) (l:Finset ℕ):
    Rendered (fun z=>Attached.packet P.activities P.p ((WilsonOriginalOccupiedTap.gallery z A).K.hard x) U l):=by
  unfold Attached.packet
  by_cases live:P.activities.admissible P.p U l
  · simp only [if_pos live]
    exact finite l (fun j z=>WilsonOriginalOccupiedTap.paint z (A.K.hard x j U)) (fun j=>affine _)
  · simp only [if_neg live]
    exact constant 0

end YM.Integration.WilsonOriginalOccupiedDegree
