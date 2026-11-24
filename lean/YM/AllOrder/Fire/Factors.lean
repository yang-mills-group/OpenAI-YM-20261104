import YM.AllOrder.Fire.Rank
/-!
# Rank tracking on Taylor through Gaussian heat step
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Finset Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory Response
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "Ω"=>X×Y
variable {E:Book X}{u:ℕ→X→ℝ}{v:X→ℝ}{n k r:ℕ}
lemma rank_law (h:∀ i,Rank X (r*i) (u i))(j:ℕ): ∀ i,Rank X (r*i) (energy u j i):=by
 induction j with
 | zero=>intro i; rw [level]; by_cases hi:i=0; subst i; exact Rank.nil _ _; rw [show wirings (fun _:X=>1) i=(fun _=>0) from funext fun _=> if_neg hi]; exact Rank.nil _ _
 | succ j ih=>
    intro i; rw [powered,show alters (energy u j) u i=∑ k∈Finset.range (i+1),energy u j k*u (i-k) from funext fun x=> by rw [plus_real,Finset.sum_apply];rfl]
    refine Rank.sum fun k hk=> ((ih k).mul (h _)).up ?_; have he : k+(i-k)=i:= (Nat.add_sub_of_le (Nat.le_of_lt_succ (mem_range.mp hk))) -- fix
    rw [← mul_add,he]
lemma rank_exp (h:∀ i,Rank X (r*i) (u i))(hx:u 0=0)(n:ℕ): Rank X (r*n) (EXP u n):= by
 rw [Expo hx (le_refl n),arrow,Finset.sum_apply]; exact Rank.sum fun i _=> (rank_law h ..).scal _
lemma rank_log (h:∀ i,Rank X (r*i) (u i))(hx:u 0=1)(n:ℕ): Rank X (r*n) (LOG u n):= by
 rw [Lords hx (le_refl n),arrow,Finset.sum_apply]; exact Rank.sum fun i _=> (rank_law (fun j=> (h j).sub ((level u) ▸ rank_law h 0 j)) i n).scal _
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
lemma impulse_rank (M:X→L[ℝ] Y)(A H:ℝ×(X×Y)→ℝ)(i:ℕ): Rank Ω (i+2) (Impulse M A H i):=by
 have hv (p j:ℕ)(A:ℝ×Ω→ℝ): Rank Ω (j+p) (spine M A p j) := by
    let G:=jet A (j+p)
    have he : Rank _ (j+p) G := Rank.scal (Rank.hom (A:=ContinuousLinearMap.id ℝ _) (f:=iteratedFDeriv ℝ (j+p) A 0)) _
    have ha:∀ x : Ω,colorful M x= ((1:ℝ), 0)+softPlane M x:=by intro x; simp [colorful,softPlane]
    unfold spine; simp_rw [ha]; exact he.app (LinearMap.toContinuousLinearMap _) _
 by_cases hi : i=0; rw [Impulse,hi,win0]; exact Rank.nil _ _
 rw [Impulse,win_atn _ hi]; exact Rank.sub ((hv 0 i (Real.log ∘ H)).up (by omega : i+0 ≤ i+2)) (hv 2 i A)
lemma cut_design (M:X→L[ℝ] Y)(A H:ℝ×(X×Y)→ℝ)(i:ℕ): Rank Ω (3*i) (Impulse M A H i):=by
 by_cases hi : i=0; rw [Impulse,hi,win0]; exact Rank.nil _ _
 exact Rank.up (impulse_rank ..) (by omega)
end YM.AllOrder.Fire
