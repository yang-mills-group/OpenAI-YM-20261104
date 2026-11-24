import YangMills.WilsonProof.NativeSupport.OriginalPattern

/-! Scale costs on the actual selected run. The division into blocks is the
same in every period and for every choice of slices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson Marker RGComparison.Core16
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MergeProof
open scoped Classical BigOperators
variable {G : Gauge}

theorem log_scale {A : Levels G} {k N per : ℕ} (T : Slices A per) (h : k ≤ N) :
    Real.log (scale (traversal T h) : ℝ)=A.S.scale N-A.S.scale k := by
  induction h using Nat.decreasingInduction with
  | self => simp [scale]
  | of_succ k hk ih =>
    have count : 0 < scale (traversal T hk) := by
      by_contra! fail
      have z:=side_scale (traversal T hk)
      rw [Nat.eq_zero_of_le_zero fail,mul_zero] at z
      exact (A.S.side N per).property.not_ge z.symm.le
    have block : 0 < ((A.S.block k).val:ℝ) := by exact_mod_cast (A.S.block k).property
    rw [traversal_push T hk,scale,Nat.cast_mul]
    change Real.log (((A.S.block k).val:ℝ)*(scale (traversal T hk):ℝ))=_
    rw [Real.log_mul block.ne' (by exact_mod_cast count.ne'),ih,Schedule.scale_succ]
    ring

theorem monotone_hat (A : Levels G) (simple : G.Simple) : Monotone A.clock.hatBeta := by
  have inc : Monotone A.S.scale := monotone_nat_of_le_succ fun j=>by
    rw [Schedule.scale_succ]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (A.S.block j).property))
  intro i j h
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (inc h) (Gauge.slopeConstant_pos simple).le)

theorem log_loss_bound (R : Run G) (simple : G.Simple) (k N s : ℕ) :
    let A:=R.alloy.B.a
    let b:=A.clock.hatBeta N
    logLoss R k N s ≤ 2*((N-k:ℕ):ℝ)*Real.log b+Real.log b/2+Real.log 4+
      ((A.budget N).supportExponent+1)*(2*(s:ℝ)+1)^4 := by
  intro A b
  have hp (j : ℕ) : 0<A.clock.hatBeta j := zero_lt_one.trans (A.fits.delayed j)
  have hlog : 0 ≤ Real.log b := Real.log_nonneg (A.fits.delayed N).le
  have er : 0 ≤ ((A.budget N).supportExponent+1)*(2*(s:ℝ)+1)^4 :=
    mul_nonneg (by linarith only [(A.budget N).exponent_pos]) (by positivity)
  have indices (j : ℕ) (_ : j ∈ Ico k N) : 0<Bandage.renal A j := Real.rpow_pos_of_pos (hp _) _
  have loss (j : ℕ) : Real.log (Bandage.renal A j)= -2*Real.log (A.clock.hatBeta (j+1)) := by
    change Real.log ((A.clock.hatBeta (j+1))^(-(2:ℝ)))=_
    rw [Real.log_rpow (hp _)]
  have walk : ∑ j∈Ico k N,2*Real.log (A.clock.hatBeta (j+1)) ≤ 2*((N-k:ℕ):ℝ)*Real.log b := by
    calc _ ≤ ∑ _j∈Ico k N,2*Real.log b := sum_le_sum fun j hj=>
                mul_le_mul_of_nonneg_left (Real.log_le_log (hp _) (monotone_hat A simple (mem_Ico.mp hj).2)) zero_le_two
         _ = _ := by simp; ring
  have far : 0<Bandage.far A N := by
    change 0<(Real.sqrt b)⁻¹/4; have hb:=hp N; positivity
  have logfar : Real.log (Bandage.far A N)= -(Real.log b/2)-Real.log 4 := by
    change Real.log ((Real.sqrt b)⁻¹/4)=_
    rw [Real.log_div (inv_ne_zero (Real.sqrt_pos.mpr (hp N)).ne') (by norm_num),Real.log_inv,Real.log_sqrt (hp N).le]
  apply max_le
  · linarith only [mul_nonneg (by positivity : 0≤2*((N-k:ℕ):ℝ)) hlog,hlog,Real.log_nonneg (by norm_num : (1:ℝ)≤4),er]
  · change -Real.log ((∏ j∈Ico k N,Bandage.renal A j)*(Bandage.far A N*Real.exp _)) ≤ _
    rw [Real.log_mul (prod_pos indices).ne' (mul_pos far (Real.exp_pos _)).ne',
      Real.log_prod (fun j hj=>(indices j hj).ne'),Real.log_mul far.ne' (Real.exp_pos _).ne',logfar,Real.log_exp]
    simp only [loss,neg_mul,Finset.sum_neg_distrib]
    linarith only [walk]

end YM.Integration.InletSusceptibility.Packet
