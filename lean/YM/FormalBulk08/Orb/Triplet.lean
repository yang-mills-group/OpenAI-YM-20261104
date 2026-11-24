import YM.FormalBulk08.Orb.Oar

/-! Finite step. Conventions: `splash` is PLUS log weight (i.e. *negative* action), order 0 already subtracts constants. It includes the Haar-on-the-tree cap. Solved carries exact Hessian and mean. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix PowerSeries
open scoped BigOperators
variable {V I J : Type*} [DecidableEq V] [Fintype V]
structure Hull (V I : Type*) [Fintype V] [DecidableEq V] where
   saddle : Saddle ℝ V
   main : TypeR I
   drift : V→TypeR I
variable (H : Hull V I) (p : Pap (V ⊕ I)) (z : I→Pap J)
-- main e0 coarse with negative precision
def fueled := Sum.elim (fun i => C (MvPolynomial.X (R:=TypeR I) i)+boost V (C (H.drift i))) (fun i:I => boost V (C (MvPolynomial.X i)))
def toInk : Pap (V ⊕ I)→+* Ink V I := roam ℝ (fueled H)
def advance := Sum.elim (fun i => C (MvPolynomial.X (R:=TypeR J) i)+boost V (roam ℝ z (C (H.drift i)))) (fun i:I => boost V (z i))
lemma teleport_toInk : teleport z (toInk H p)=roam ℝ (advance H z) p := by
   unfold teleport toInk roam advance
   rw [change_comp]
   have h : changeBy (tri z V)=teleport z := rfl
   rw [h]
   rw [show (teleport z).comp (insertAt ℝ (fueled H))=_ from ?hex]
   case hex =>
      ext
      case hC r n m a => simp [tri,boost] -- branch
      case hX i n m a=> cases i <;> simp [fueled, teleport_boost,tri,roam]

def Solved := coeff 0 (toInk H p)= (variation H.saddle I).base + MvPolynomial.C H.main
def positive := toInk H p-C ((variation H.saddle I).base)-boost V (C H.main)
def vocal := beam (variation H.saddle I).call (expan (positive H p))
def out := C H.main+covelog (vocal H p)
def flag (q : Pap (V ⊕ I)) := expan (-(covelog (vocal H p))) * beam (variation H.saddle I).call (expan (positive H p)*toInk H q)
section
variable (hp : Solved H p)
include hp
lemma plur : coeff 0 (positive H p)=0 := by unfold Solved at hp; rw [positive,map_sub,map_sub,hp]; simp [boost]
lemma voice : coeff 0 (vocal H p)=1 := by rw [vocal,coeff_beam,expan_zero (plur H p hp),Saddle.call,moment_one]
lemma out_main : coeff 0 (out H p)=H.main := by rw [out,map_add,covelog_rank (voice H p hp),add_zero]; simp
lemma normalization (q : Pap (V ⊕ I)) : vocal H p * flag H p q = beam (variation H.saddle I).call (expan (positive H p)*toInk H q) := by
   unfold flag; rw [←mul_assoc]; conv_lhs => arg 1;lhs;rw [←expan_after (p:=vocal H p) (voice H p hp)]
   have hh:= covelog_rank (voice H p hp)
   rw [expan_mul hh (by rw [map_neg,hh,neg_zero]),add_neg_cancel,root_expan,one_mul]
end
lemma positive_eq : toInk H p = C ((variation H.saddle I).base)+boost V (C H.main)+positive H p := by unfold positive; abel
end YM.FormalBulk08.Orb
