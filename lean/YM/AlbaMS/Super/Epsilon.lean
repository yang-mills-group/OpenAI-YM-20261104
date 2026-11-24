import YM.AlbaMS.Super.Firm
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.NormNum.Basic
/-!
Linear path parameter, exact on nil order systems. Not analytic ε!
Later d calculations may use a formal scale path besides physical ε.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function IsNilpotent Polynomial
open scoped BigOperators Classical Polynomial
variable {ι R T : Type*} [CommRing R] {ρ : ι→Bool} (p : Bool)
variable (Y U : Coil ρ R[X]) (F : Coil ρ R)(P : ℕ→Coil ρ R) {l : List ι} (k : ι→ι→R) (s : Finset ι) (m n : ℕ)

def line (ρ : ι→ Bool)(c : R) := Wind ρ (evalRingHom c)
def next (k : ι→ι→R): ι→ι→ R[X] := fun i j=> C (k i j)
def derive : Coil ρ R[X]→+Coil ρ R[X] := seep Polynomial.derivative.toAddMonoidHom
def atom (n : ℕ) : Coil ρ R[X] →+ Coil ρ R:= seep (lcoeff R n).toAddMonoidHom
def path (N : ℕ)(P : ℕ→Coil ρ R): Coil ρ R[X]:= ∑ i∈Finset.range (N+1), (X:R[X])^i • Wind ρ C (P i)

lemma derives : lever (derive (ρ:=ρ) (R:=R)):=by
  intro F G h; rw [add_comm]; exact seep_derive F G _ fun x y=> by change derivative _=derivative x*_+_*derivative y; rw [derivative_mul] -- RHS orientation
lemma atom_touch : atom n (touch (next k) s Y)= touch k s (atom n Y):= seep_touch Y _ fun _ _ _=> coeff_C_mul ..
lemma atom_cross (h:Graded ρ p k): atom n (cross p (next k) s Y U) = ∑ i∈ Finset.antidiagonal n, cross p k s (atom i.1 Y) (atom i.2 U):=
  seep_many_cross (L:=k) (k:=next k) (s:=s) p Y U (lcoeff R n).toAddMonoidHom (Finset.antidiagonal n) (fun i =>(lcoeff R i.1).toAddMonoidHom) (fun i=>(lcoeff R i.2).toAddMonoidHom) (fun x y=> coeff_mul x y n)
    (fun i j he=>h i j (fun ha=> he (by simp [next,ha]))) h fun i j f=> by exact coeff_C_mul ..
lemma atoms (h:∀ n,atom n Y=atom n U):Y=U:= Coil.ext _ _ fun l=> Polynomial.ext fun n=> DFunLike.congr_fun (h n) l
lemma step : atom n (derive Y)=((n+1:ℕ):R) • atom (n+1) Y:= by ext l; change coeff (derivative (Y l)) n=_*_; rw [coeff_derivative]; simp [mul_comm]; rfl
lemma line_read (b:R) : line ρ b Y l=(Y l).eval b:=rfl
lemma atom_read : atom n Y l = (Y l).coeff n:=rfl
@[simp] lemma beg : line ρ 0 Y=atom 0 Y:=by ext l; simp [line_read,atom_read, ← coeff_zero_eq_eval_zero]
lemma path_atom (h:∀ i,n<i→ P i=0): atom m (path n P)= P m:=by
  ext l; unfold path; rw [map_sum,sum_read]; simp_rw [atom_read,smul_read,blows,seep_read];
  simp; intro hh; simp [h _ hh] -- need direct monomial
lemma path_stop : line ρ 1 (path n P)= ∑ i∈Finset.range (n+1), P i:=by
  rw [path,map_sum]; apply Finset.sum_congr rfl; intro i _; ext l; rw [line_read,smul_read,eval_mul,blows,seep_read];change _*(C _).eval 1=_; simp
lemma Tone.path (H:∀ i,Tone p (P i)):Tone p (path n P):= by unfold Coil.path; refine Tone.sum _ _ fun i _=>?_ ; rw [blows]; exact ((H i).seep _ _ _).smul _
lemma Cap.path (H:∀ i,Cap (P i) m): Cap (path n P) m:= by unfold Coil.path; refine Cap.sum _ _ fun i _=>?_ ; rw [blows]; exact ((H i).seep _ _).smul _
lemma next_graded (h:Graded ρ p k): Graded ρ p (next k) := fun i j he=> h i j (fun hv=> he (by simp [next,hv]))

variable [Algebra ℚ R]
omit [Algebra ℚ R] in
lemma path_nil (h:∀ i,Tone false (P i))(H:∀ i, IsNilpotent (P i)): IsNilpotent (path n P):= by
  unfold path; apply Commute.isNilpotent_sum (fun i _ => ((H i).map (Wind ρ C)).smul _); intro i hi j hj; rw [blows (F:=P i)]; exact (((h i).seep _ _ _).smul _).skim _
lemma step_cross (h:Graded ρ false k) (H:∀ i,n<i→ P i=0) (ht:∀ j, ((j+1:ℕ):R) • P (j+1)=touch k s (P j)-halve R • ∑ i∈ Finset.antidiagonal j,cross false k s (P i.1) (P i.2)) (a:path n P=Y): derive Y=touch (next k) s Y-halve R[X] • cross false (next k) s Y Y:=by
  subst Y; apply atoms; intro i; rw [map_sub, step,atom_touch, path_atom _ _ _ H, path_atom _ _ _ H]; simp_rw [ht i]; unfold halve; simp_rw [algebraMap_smul,map_rat_smul,atom_cross false _ _ k s i h]; simp_rw [path_atom _ _ _ H]
end YM.MSBar.Bric.Coil
