import YM.Integration.WilsonMatrixOriginalDeckRawPanel
import Mathlib.RingTheory.Nilpotent.Basic

/-! The true all-glyph zeroth fee matrix is invertible by its original triangular field grading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescription
open Finset MS MS.Land MS.Menus MS.Local.Physical
open scoped Classical BigOperators Matrix
variable {G:Gauge}{B:Deck G} (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

def resized {d e:ℕ}(j:Glyph B d)(fits:j.size≤e):Glyph B e:= ⟨⟨j.size,by omega⟩,j.2⟩

private theorem restored (a b:I)(fits:b.size≤a.size):resized b fits=MS.Land.read a.2 ↔ b=a:=by
  constructor
  · intro eq
    have bound:a.size≤h:=Nat.le_of_lt_succ a.1.isLt
    have up:=congrArg (fun j:Glyph B a.size=>resized j (Nat.le_trans (Nat.le_of_lt_succ j.1.isLt) bound)) eq
    exact up
  · rintro rfl;rfl

def fees (μ:ℝ)(k:ℕ):Matrix I I ℂ:=fun b a=>
  if fits:b.size≤a.size then oil (Q.fees a.size a.2) (resized b fits) k μ else 0

theorem upper (μ:ℝ)(b a:I)(above:a.grade≤b.grade):fees Q h μ 0 b a=if b=a then 1 else 0:=by
  by_cases fits:b.size≤a.size
  · rw [fees,dif_pos fits,oil,(Q.init a.size a.2).Single (resized b fits) above]
    by_cases eq:b=a
    · rw [if_pos ((restored (B:=B) h a b fits).2 eq),if_pos eq];simp
    · rw [if_neg ((restored (B:=B) h a b fits).not.mpr eq),if_neg eq];simp
  · have ne:b≠a:=by rintro rfl;exact fits le_rfl
    simp [fees,fits,ne]

private theorem drops {A:Matrix I I ℂ}(strict:∀i j:I,j.grade≤ i.grade→ A i j=0) (n:ℕ):
    ∀i j:I,j.grade< i.grade+n→(A^n) i j=0:=by
  induction n with
  | zero =>
    intro i j less
    have ne:i≠j:=by rintro rfl;omega
    simp [ne]
  | succ n ih =>
    intro i j less
    rw [pow_succ,Matrix.mul_apply]
    apply sum_eq_zero
    intro l _
    by_cases low:l.grade< i.grade+n
    · rw [ih i l low,zero_mul]
    · rw [strict l j (by omega),mul_zero]

/-- Every lower-grade term, also across different nominal sizes, participates in this actual inversion. -/
theorem original (μ:ℝ):IsUnit (fees Q h μ 0):=by
  let A:=1-fees Q h μ 0
  have strict(i j:I)(hj:j.grade≤ i.grade):A i j=0:=by simp [A,Matrix.one_apply,upper Q h μ i j hj]
  have nil:IsNilpotent A:=by
    refine ⟨h+1,?_⟩;ext i j
    exact drops h strict (h+1) i j (by have:=j.memory;omega)
  simpa [A] using nil.isUnit_one_sub

end YM.Integration.WilsonMatrixOriginalDeckPrescription
