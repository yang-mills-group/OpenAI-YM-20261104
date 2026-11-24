import YM.Frontier6.Bouquet.Geometry.Differences
import YM.Frontier6.Normal.Stripping

/-! Directional method of measuring anisotropic tests. Directions always
 identified in the common ambient slots. Utility functions totalized by orth
 projection; guards state directions in the relevant subspaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {V X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
namespace Anise
section
-- Full linear tests
variable (x u : X)(f:Full X)
def step (v:X): Full X →ₗ[ℂ] Full X:= (TestFunction.lineDerivCLM ℂ v : Full X →L[ℂ] Full X).toLinearMap
lemma step_cast : (step u f:X→ℂ)= Analysis.D u f:=by ext1 x; change (TestFunction.lineDerivCLM ℂ u f : Full X) x=_; rw [TestFunction.lineDerivCLM_eq_fderivCLM]; simp [TestFunction.fderivCLM_apply_of_le, Analysis.D]
lemma step_support : tsupport (step u f)⊆tsupport f:=by rw [step_cast]; exact tsupport_fderiv_apply_subset ℝ u
lemma step_comm : step u (step x f)=step x (step u f):=by
   ext1 v; simp_rw [step_cast]; apply Analysis.commuteD; exact (Normal.charge_smooth f.contDiff 2|>.contDiffAt) -- coe levels defin?
end

def path : List X→ Full X →ₗ[ℂ] Full X
| [] => LinearMap.id
| x::xs => step x ∘ₗ path xs
variable (u v:List X)(f:Full X)
@[simp] lemma path_nil : path [] f=f:= rfl
lemma path_cons (x:X) : path (x::u) f=step x (path u f):=rfl
lemma path_zip : path (u++v) f=path u (path v f):=by induction u with
   | nil=>rfl
   | cons x u ih=>rw [List.cons_append,path_cons,path_cons,ih]
lemma path_perm (h:u.Perm v): path u f=path v f:= by
    induction h with
    | nil=> rfl
    | cons x h ih=> rw [path_cons,path_cons,ih]
    | swap x y l=> simp_rw [path_cons]; exact step_comm ..
    | trans _ _ ih jh=> rw [ih,jh]
lemma path_support : tsupport (path u f) ⊆ tsupport f:=by induction u with
    | nil=> exact Subset.rfl
    | cons x u ih=> rw [path_cons]; exact (step_support ..).trans ih
-- arbitrary permutations $Multiset$
def sequence (s:Multiset X): Full X→ₗ[ℂ] Full X:= path s.toList
lemma sequences (s:Multiset X)(u:List X)(he:s=u):sequence s f=path u f:= path_perm _ _ f (Multiset.coe_eq_coe.mp ((s.coe_toList).trans he)) -- syntax
lemma sequence_zero : sequence 0 f=f:=by simp [sequence]
lemma sequence_list : sequence (u:Multiset X) f=path u f:= sequences f _ _ rfl
lemma sequence_add (s t:Multiset X) : sequence (s+t) f=sequence s (sequence t f):=by
    rw [sequences f _ (s.toList++t.toList) (by change s+t= (s.toList:Multiset X) + (t.toList:Multiset X); simp)]; exact path_zip ..
-- every tensor derivative exactly
lemma path_fn (n:ℕ)(p:Fin n→ X): (path (List.ofFn p) f:X→ℂ)=(fun x=>iteratedFDeriv ℝ n f x p):=by
   induction n with
   | zero=> simp
   | succ n ih=>
         rw [List.ofFn_succ, path_cons, step_cast, ih]; ext1 x
         have h:= Analysis.cons_jet (x:=x) (Normal.charge_smooth f.contDiff (n+1)|>.contDiffAt) (p 0) (Fin.tail p); rw [Fin.cons_self_tail] at h; exact h.symm
end Anise

section
variable (P:Place)[FiniteDimensional ℝ P]
abbrev ontoSpace : Room→L[ℝ] P:= by
   letI:= FiniteDimensional.complete ℝ P
   exact P.orthogonalProjectionOnto
def ride (x:Room): Full P →ₗ[ℂ] Full P:= Anise.step (ontoSpace P x)
def pedal (p:List Room): Full P→ₗ[ℂ] Full P:= Anise.path (p.map (ontoSpace P))
def train (p:Multiset Room): Full P→ₗ[ℂ] Full P:= Anise.sequence (p.map (ontoSpace P))
variable {P}
lemma on_home (x:P): ontoSpace P x.val=x:= by
    letI:=FiniteDimensional.complete ℝ P; exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ..
lemma step_in (u:P)(f:Full P) : ride P u.val f=Anise.step u f:=by unfold ride; rw [on_home]
lemma train_list (u:List Room)(f:Full P): train P (u:Multiset Room) f=pedal P u f:= Anise.sequence_list ..
lemma train_support (p:Multiset Room)(f:Full P): tsupport (train P p f)⊆tsupport f:= Anise.path_support ..
lemma trains_add (s t:Multiset Room)(f:Full P): train P (s+t) f=train P s (train P t f):=by unfold train; rw [Multiset.map_add]; exact Anise.sequence_add ..
lemma trains_zero (f:Full P):train P 0 f=f:=by unfold train; rw [Multiset.map_zero, Anise.sequence_zero]
end
end YM.Frontier6.Bouquet
