import YM.AlbaMS.Pockets.Pressure

/-!
Capability of finite s physical PT graphs: iterate linear band recursion
with same mask interpretation on all input data and keep receipt for steps to
compute rank-zero Log values. No repeated signs on kernels touched.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function IsNilpotent
open scoped BigOperators Classical
variable {ι K W R : Type*} [Fintype K] [AddCommMonoid W] [CommRing R] [Algebra ℚ R] {ρ : ι→Bool}
open Coil
namespace Ladder
variable {F G : Coil ρ R} {D : Ladder K W} {U V:Coil ρ (Tags D R)} {g : ι→ι→R} {p : Bool} {x : K} {a b m n : ℕ} {s : Finset ι}
structure Closed (D : Ladder K W)(b:ℕ)(U : Coil ρ (Tags D R)) : Prop where
   tone : Tone false U
   cap x : Cap (clip D x U) (b*D.d x)
   zero : clip D D.ort U=0
lemma evolution (h:Tone false F)(hv:Graded ρ false g): Tone false (ev g s F n):=by
  induction n using Nat.strong_induction_on with | h n ih=>
    cases n; rw [ev]; exact h
    next j=>
      rw [ev_succ,brink]; refine (Tone.sub (touch_tone _ false _ _ _ (ih j (by omega)) hv) (Tone.smul ?_ _)).smul _
      refine Tone.sum _ _ (fun i hi=>?_); rw [Finset.mem_antidiagonal] at hi; exact tone_cross _ _ _ _ _ (ih i.1 (by omega)) (ih i.2 (by omega)) hv
lemma asset (hv:Graded ρ false g)(C:Closed D b U): Closed D b (ev (D.rail g) s U n):= ⟨evolution C.tone (lines hv), fun x=> (electric (fun x=> Thin.cheap (C.cap x)) hv).cap,by
  cases n; rw [ev,C.zero]; apply Thin.impossible (electric (fun x=> Thin.cheap (C.cap x)) hv); rw [D.d0,Nat.mul_zero]; omega⟩
omit [Algebra ℚ R] in
lemma Closed.rank (C:Closed D b U) : Cap U (b*D.fuel):=by rw [reload (U:=U)]; apply total_cap; intro i; exact (C.cap i).up (Nat.mul_le_mul_left _ d_le)
omit [Algebra ℚ R] in
lemma Closed.dead (C:Closed D b U): IsNilpotent U:= Silent.nil C.zero
lemma ev_end (C:Closed D b U)(hv:Graded ρ false g)(h:b*D.fuel<2*n): ev (D.rail g) s U n=0:=
  ext_rail fun i=> ((electric (fun x=> Thin.cheap (C.cap x)) hv).impossible (lt_of_le_of_lt (Nat.mul_le_mul_left _ (d_le (x:=i))) h)).trans (map_zero _).symm

def total (D : Ladder K W)(b:ℕ)(g:ι→ι→R)(s:Finset ι)(U : Coil ρ (Tags D R)):=∑ j∈ Finset.range (b*D.fuel+1), ev (D.rail g) s U j
lemma seat (C:Closed D b U)(hv:Graded ρ false g): Closed D b (total D b g s U):=by
  refine ⟨Tone.sum _ _ fun j _=> (asset hv C).tone, fun x=>?_,?_⟩
  · rw [total,map_sum]; exact Cap.sum _ _ fun j _=> (asset hv C).cap x
  rw [total,map_sum]; exact Finset.sum_eq_zero fun j _=> (asset hv C).zero
lemma ord_flow (C:Closed D b U)(hv:Graded ρ false g): exp (-total D b g s U)= wither (D.rail g) s (exp (-U)):=by
  let P:=ev (D.rail g) s U; have he:P 0=U:=by unfold P; rw [ev];
  have hh j:Closed D b (P j):=asset hv C; let N:=b*D.fuel
  refine (logs (s:=s) (n:=N) (P:=P) (lines hv) (fun i hi=>ev_end C hv (by omega : N<2*i)) (fun i=> (hh i).tone) (fun i=>(hh i).dead) (fun j=> ?_) ⟨_,(hh 0).rank⟩).trans ?_
  · unfold P; rw [ev_succ,brink,smul_smul,patch_succ,one_smul]
  rw [he]
lemma step_total (x:K):clip D x (total D b g s U)= clip D x U+∑ j∈Finset.range (b*D.fuel), clip D x (ev (D.rail g) s U (j+1)):=by rw [total, map_sum, Finset.sum_range_succ', ev, add_comm]
lemma step_ev (hv:Graded ρ false g):clip D x (ev (D.rail g) s U (n+1))=Track0 D g s (fun j x=> clip D x (ev (D.rail g) s U j)) n x:=by rw [ev_succ,brinks hv]
end Ladder
end YM.MSBar.Bric
