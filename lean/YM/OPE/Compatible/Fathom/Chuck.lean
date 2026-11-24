import YM.OPE.Compatible.Fathom.Awake
import YM.OPE.Compatible.Straws.Stoop
/-!
# Polynomial test degree and scalar IBP. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {I J:Type}{i j k r:ℕ}
local notation "V!"=> Module.Dual ℝ E
variable {p q z:E→ℝ}
open Tensor Analysis ContinuousMultilinearMap
theorem hatCoeff (A : T E F j) (ha : Sym A) : coeff (diagonal A) j 0 = A := by
  apply ContinuousMultilinearMap.ext; intro u
  induction j with
  | zero => rw [coeff_apply_zero]; exact congr_arg A (Subsingleton.elim ..)
  | succ j ih =>
    rw [← Fin.cons_self_tail u]
    let v := u 0
    let s := Fin.tail u
    let B := A.curryLeft v
    let t : ℝ := (↑(j+1 : ℕ) : ℝ)
    have he : D v (diagonal A) = t • diagonal B := funext fun x => by
      rw [D,differential_diagonal A ha]
      change _ = (↑(j+1 : ℕ) : ℝ) • (diagonal B x)
      rw [Nat.cast_smul_eq_nsmul]; rfl
    have hs := ih B (freeze_sym A ha v) s
    have ht : t ≠ 0 := by dsimp [t]; positivity
    change coeff (diagonal A) (j+1) 0 (Fin.cons v s) = _
    rw [coeff_apply_cons (diag_smooth A _ |>.contDiffAt),he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply,hs]
    change t⁻¹ • t • B s = _
    rw [inv_smul_smul₀ ht]
    rfl

theorem hatCoeff_ne (A : T E F j) (ha : Sym A) (hh : k ≠ j) :
    coeff (diagonal A) k 0 = 0 := by
  apply ContinuousMultilinearMap.ext; intro u
  induction k generalizing j with
  | zero =>
    rw [coeff_apply_zero]
    cases j with
    | zero => exact (hh rfl).elim
    | succ j =>
      change A _ = (0:F)
      exact A.map_coord_zero (0 : Fin (j+1)) rfl
  | succ k ih =>
    rw [← Fin.cons_self_tail u, coeff_apply_cons (diag_smooth A _ |>.contDiffAt)]
    cases j with
    | zero =>
      rw [show diagonal A = fun _ => diagonal A 0 from
        funext fun _ => congr_arg A (Subsingleton.elim ..)]
      have hz : D (u 0) (fun _ => diagonal A 0) = fun _ => (0:F) := by simp [D, funext_iff]
      rw [hz, coeff_zero]; simp
    | succ j =>
      let v := u 0
      let B := A.curryLeft v
      have he : D (u 0) (diagonal A) = (↑(j+1 : ℕ) : ℝ) • diagonal B := funext fun x => by
        rw [D,differential_diagonal A ha];
        change _ = (↑(j+1 : ℕ) : ℝ) • (diagonal B x)
        rw [Nat.cast_smul_eq_nsmul]; rfl
      rw [he, Tensor.coeff_smul _ (diag_smooth _ _ |>.contDiffAt), smul_apply, ih B (freeze_sym A ha v) (by omega)]
      simp
lemma gradeC {p:Song E} (h:p∈ harmon E j) (k:ℕ): coeff (Strike j p) k 0=p k:=by
      let g(n:ℕ):=diagonal (p n); have hp(n:ℕ): ContDiffAt ℝ k (g n) 0:= (diag_smooth _ _).contDiffAt; have hh(n:ℕ):Tensor.Sym (p n):=h.2 n; rw [show Strike j p= (∑ n∈range (j+1),g n) from funext fun i=>by rw [Finset.sum_apply],Tensor.coeff_sum k 0 _ _ fun i _=>hp i]; by_cases hk:k ≤ j
      · rw [sum_eq_single k]; exact hatCoeff _ (hh _); exact fun b _ hb=>hatCoeff_ne _ (hh _) hb.symm; exact fun hx=>(hx (mem_range.mpr (by omega))).elim
      rw [(show ∀ i:ℕ,_ from (show ∀ i:ℕ,i>j→p i=0 from h.1)) k (by omega)]; exact sum_eq_zero fun i hi=>hatCoeff_ne _ (hh _) (by have h:=mem_range.mp hi;omega)
-- movement wake
end YM.OPE.Cloud
