import YM.Integration.FVA1Physical.Wilson.ExteriorRate
import YM.MSbar.Bakery.Power

/-! An independently chosen background at every spatial derivative word
may have an arbitrary rough exterior. Retaining half of the exponential
and the full polynomial support weight pays all remote first differences
at once, using the same anchored vault as the normalized Wilson step. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Set Metric MvPolynomial Lattice
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Bakery
open scoped Classical Topology ContDiff
variable {σ : Type} [Fintype σ] {n : Side}

omit [Fintype σ] in
private theorem split_weight (loc : σ→Site n) (b : Site n) (s R : ℕ) {a : ℝ}
    (ha : 0 ≤ a) (L : List σ) (i : σ) (far : R ≤ separation b (loc i)) :
    spread loc {b} (a/2) s L ≤ Real.exp (-(a/2*(R:ℝ)))*spread loc {b} a s (L++[i]) := by
  let D:=extent (zone loc {b} L)
  let E:=extent (zone loc {b} (L++[i]))
  have le : D ≤ E := by
    apply intr
    unfold zone
    simp [Finset.subset_iff]
    grind
  have re : R ≤ E := far.trans (curve (Finset.mem_union_left _ (mem_singleton_self b))
    (Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,by simp,rfl⟩))))
  have sum : a/2*(D:ℝ) ≤ -(a/2*(R:ℝ))+a*E := by
    have d := mul_le_mul_of_nonneg_left ((Nat.cast_le (α:=ℝ)).mpr le) (div_nonneg ha zero_le_two)
    have r := mul_le_mul_of_nonneg_left ((Nat.cast_le (α:=ℝ)).mpr re) (div_nonneg ha zero_le_two)
    linarith
  change (1+(D:ℝ))^s*Real.exp (a/2*D) ≤ Real.exp (-(a/2*(R:ℝ)))*((1+(E:ℝ))^s*Real.exp (a*E))
  rw [mul_left_comm,←Real.exp_add]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left le 1 : (1:ℝ)+D ≤ 1+E) s)
    (Real.exp_le_exp.mpr sum) (Real.exp_pos _).le (by positivity)

theorem rough_independent_words (loc : σ→Site n) (b : Site n) (m s k R : ℕ) {a B K : ℝ}
    (ha : 0 ≤ a) (f : Pot σ) (deg : f.totalDegree ≤ m)
    (paid : Vault loc {b} a s m 0 f B) (X Y : List σ→View σ)
    (hK : 0 ≤ K) (hX : ∀ L, ‖X L‖ ≤ K) (hY : ∀ L, ‖Y L‖ ≤ K)
    (same : ∀ L i,separation b (loc i)<R → X L i=Y L i) :
    Yarn k (fun L=>spread loc {b} (a/2) s L*|read (Y L) L f-read (X L) L f|) ≤
      Real.exp (-(a/2*(R:ℝ)))*(2*K*(B*(1+K)^(m+1))) := by
  let U:=closedBall (0:View σ) K
  let F:=fun x=>MvPolynomial.eval x f
  let t:=Real.exp (-(a/2*(R:ℝ)))
  have fund:=spice_fund ha deg paid hK (k+1)
  have changeAt (L : List σ) : ∃ z∈U,
      glance F L (Y L)-glance F L (X L)=∑ i:σ,(Y L i-X L i)*glance F (L++[i]) z :=
    cutAt L (convex_closedBall ..) (mem_closedBall_zero_iff.mpr (hX L)) (mem_closedBall_zero_iff.mpr (hY L))
      (fun _ _=>(vent f).contDiffAt.of_le (by simp))
  choose z hz eq using changeAt
  have motion (L) : ‖Y L-X L‖ ≤ 2*K := (norm_sub_le ..).trans ((add_le_add (hY L) (hX L)).trans_eq (two_mul K).symm)
  have word (L : List σ) : spread loc {b} (a/2) s L*|read (Y L) L f-read (X L) L f| ≤
      (t*(2*K))*∑ i:σ,value loc {b} a s (z L) F (L++[i]) := by
    rw [←glance_jet f L,←glance_jet f L,eq L]
    refine (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs ..) (effect ..).le).trans ?_
    rw [mul_sum,mul_sum]
    apply sum_le_sum
    intro i _
    by_cases zero : Y L i=X L i
    · rw [zero,sub_self,zero_mul,abs_zero,mul_zero]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))
        (mul_nonneg (effect ..).le (abs_nonneg _))
    have far : R ≤ separation b (loc i) := by by_contra! hi;exact zero (same L i hi).symm
    rw [abs_mul]
    unfold value
    have diff : |Y L i-X L i| ≤ 2*K := (norm_le_pi_norm (Y L-X L) i).trans (motion _)
    calc spread loc {b} (a/2) s L*(|Y L i-X L i| *|glance F (L++[i]) (z L)|)
           ≤ (t*spread loc {b} a s (L++[i]))*((2*K)*|glance F (L++[i]) (z L)|) :=
              mul_le_mul (split_weight loc b s R ha L i far)
                (mul_le_mul_of_nonneg_right diff (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                (mul_nonneg (Real.exp_pos _).le (effect ..).le)
         _ = _ := by ring
  apply (shiny k (fun L _=>word L)).trans
  rw [sheen k,scarves (ι:=σ),←mul_assoc t (2*K) (B*(1+K)^(m+1))]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Real.exp_pos _).le (by positivity))
  let Z (W : List σ):=z W.dropLast
  have samePoint (i:σ) (L:List σ) : value loc {b} a s (z L) F (L++[i])=value loc {b} a s (Z (L++[i])) F (L++[i]) := by
    unfold Z; simp
  conv_lhs => arg 2; ext; arg 2; ext; rw [samePoint]
  exact (bothEnds k (fun L=>value loc {b} a s (Z L) F L)).trans_le (fund.2 Z fun L=>hz _)

end YM.Integration.FVA1Physical.Wilson
