import Mathlib.LinearAlgebra.Multilinear.Basic
/-! Two blocks of a multilinear kernel. Uses the Near and Far argument order of `forest`.
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Function Fin
variable {R E W : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid W]
  [Module R E] [Module R W] {n m : ℕ}

section
omit [AddCommMonoid E]
private lemma opposite (i : Fin n) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  replace h := congrArg Fin.val h
  change i.val = n+j.val at h
  omega
private lemma left_update (v : Fin n → E) (w : Fin m → E) (i : Fin n) (x : E) :
    append (update v i x) w = update (append v w) (castAdd m i) x := by
  funext j
  induction j using Fin.addCases with
  | left j => by_cases h : j = i
              · subst j; rw [Fin.append_left, update_self, update_self]
              rw [update_of_ne (show castAdd m j ≠ castAdd m i from
                    (Fin.castAdd_injective n m).ne h), Fin.append_left, Fin.append_left,
                    update_of_ne h]
  | right j => rw [update_of_ne (Ne.symm (opposite i j)), Fin.append_right, Fin.append_right]
private lemma right_update (v : Fin n → E) (w : Fin m → E) (j : Fin m) (x : E) :
    append v (update w j x) = update (append v w) (natAdd n j) x := by
  funext i
  induction i using Fin.addCases with
  | left i => rw [update_of_ne (opposite i j), Fin.append_left, Fin.append_left]
  | right i => by_cases h : i = j
               · subst i; rw [Fin.append_right, update_self, update_self]
               rw [update_of_ne (show natAdd n i ≠ natAdd n j from (Fin.natAddEmb n).injective.ne h),
                    Fin.append_right, Fin.append_right, update_of_ne h]
end
variable (B : MultilinearMap R (fun _ : Fin (n+m) => E) W)

def freezeFar (w : Fin m → E) : MultilinearMap R (fun _ : Fin n => E) W :=
  .mk' (fun v => B (Fin.append v w))
    (by intro v i x y; simp_rw [left_update]; exact B.map_update_add ..)
    (by intro v i z x; simp_rw [left_update]; exact B.map_update_smul ..)

def freezeNear (v : Fin n → E) : MultilinearMap R (fun _ : Fin m => E) W :=
  .mk' (fun w => B (Fin.append v w))
    (by intro w i x y; simp_rw [right_update]; exact B.map_update_add ..)
    (by intro w i z x; simp_rw [right_update]; exact B.map_update_smul ..)
lemma freezeFar_eq (v : Fin n → E) (w : Fin m → E) : freezeFar B w v = B (Fin.append v w) := rfl
lemma freezeNear_eq (v : Fin n → E) (w : Fin m → E) : freezeNear B v w = B (Fin.append v w) := rfl
end
end YM.FVA2.GradedFar
