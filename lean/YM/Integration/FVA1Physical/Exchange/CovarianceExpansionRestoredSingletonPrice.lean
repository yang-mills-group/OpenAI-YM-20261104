import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionSignedOldSquareObservation
import YM.Integration.FVA1Physical.CommonCover.NormalizedCrossing

/-! Eliminate the appearance of a hard-singleton RMS as an independent
input to the finite-regulator signed bill. The actual paid regular row is
charged at its own site before all tests. Consequently a gross bound F on
the true *full physically normalized* singleton gives the pointwise and
second-moment bounds for its complete gas-normalized hard row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Function Finset Set MeasureTheory Lattice RG YM.Wilson Marker QuadraticLocal Ac
open Push.AbsoluteSums QuadraticLocal.Fusion.Attached
open scoped Classical BigOperators

section Regular
variable {G:Gauge}{V I T:Type}[DecidableEq V]{D:Census V}{n:Side}{P:BudgetPoint}{o:V→Site n}
  (L:Lamps T I G P o D){w:V→ℝ}{σ a:ℝ}

-- The unscaled summation is the already accepted CommonHull.OldReadout.paid_arm
-- proof, replayed with only the present Gallery dependencies.
private theorem paid_regular_coeff (fund:L.Paid w P.B σ a) (pos:∀j,0<w j) (nn:0≤σ) (j:V) (t:T) (U:Config G n):
    ‖(L.log t U).part (D.fire j)‖ ≤ (w j)⁻¹*a:=by
  let s:=D.fire j
  obtain ⟨f,hf,bounds,byRoot⟩:=fund.budget
  have live : SumBudget (fun i=>w j*‖(L.frame i t U).part s‖) a:=by
    refine budget_mono (byRoot (o j)) (fun _=>mul_nonneg (pos j).le (norm_nonneg _)) ?_
    intro i
    by_cases hit:s=L.mode i
    · have occurs:o j∈L.ground i:=L.roots i j (hit ▸ (by simp [s,Census.fire]))
      rw [if_pos occurs,Lamps.frame,Poly.part_send,if_pos hit]
      dsimp only
      rw [←hit,Poly.solo_toll]
      have size:=L.light_size i t U (bounds i t _ (L.address i).anchor)
      exact (mul_le_mul_of_nonneg_left size (pos j).le).trans (le_mul_of_one_le_right
        (mul_nonneg (pos j).le (hf i)) (Real.one_le_exp (mul_nonneg nn (Nat.cast_nonneg _))))
    · simp only [Lamps.frame,Poly.part_send,if_neg hit,norm_zero,mul_zero]
      exact (byRoot (o j)).1 i
  have absCost:SumBudget (fun i=>‖(L.frame i t U).part s‖) ((w j)⁻¹*a):=by
    convert budget_scale (inv_nonneg.mpr (pos j).le) live using 1
    funext i
    simp [(pos j).ne']
  rw [Lamps.log,Poly.share (fund.sums nn pos t U) s]
  exact (norm_tsum_le_tsum_norm absCost.2.1).trans absCost.2.2

end Regular

variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

theorem restored_singleton_price {w:V→ℝ}(wp:∀v,0<w v){e c κ:ℝ}
    (paid:A.Pays w e c κ)(en:0≤e)(t:T)(U:Config G n)(live:0<P.eval U)(a:V)(F:ℝ)
    (physical:‖(w a:ℂ)*(((P.eval U:ℂ)⁻¹ • A.density t U).part (C.fire a))‖≤F):
    ‖(w a:ℂ)*originalRaw A t (C.fire a) U‖≤F+c:=by
  have reg:‖(w a:ℂ)*(A.E.log t U).part (C.fire a)‖≤c:=by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (wp a).le]
    exact (mul_le_mul_of_nonneg_left (paid_regular_coeff A.E paid.budget wp en a t U) (wp a).le).trans_eq
      (by rw [←mul_assoc,mul_inv_cancel₀ (wp a).ne',one_mul])
  have q:=Crossing.normalized_singleton_cost A wp paid en t U live a F c physical reg
  have vac:0<P.activities.gas P.p U:=pos_of_mul_pos_right live (Real.exp_nonneg _)
  simpa only [originalRaw,Crossing.rawSingleton,mul_div_assoc,norm_div,Complex.norm_real,Real.norm_of_nonneg vac.le,
    norm_mul] using q

omit [Fintype V] in
theorem restored_singleton_borel {w:V→ℝ}(wp:∀v,0<w v){e κ:ℝ}
    (paid:A.K.Paid w P.p.B e κ)(en:0≤e)(t:T)(a:V):
    Measurable (fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U):=by
  have fm:Measurable (A.gas t):=by
    apply Measurable.tsum
    intro s
    unfold packet
    exact Measurable.ite (P.activities.admissible_borel ..) (Finset.measurable_fun_prod _ fun i _=>(A.K.locality t i).borel) measurable_const
  have quiet(U):(A.gas t U).part C.quiet=(P.activities.gas P.p U:ℂ):=
    Hard.packet_of_quiet A.K t U (Hard.packet_summing _ paid en wp t U)
  have qm:Measurable (fun U=>(P.activities.gas P.p U:ℂ)):=by
    have m:Measurable (fun U=>(A.gas t U).part C.quiet):=(Poly.part_cont C.quiet).measurable.comp fm
    simpa only [quiet] using m
  exact measurable_const.mul (((Poly.part_cont _).measurable.comp fm).div qm)

theorem restored_singleton_square (μ:Measure (Config G n))[IsFiniteMeasure μ]
    {w:V→ℝ}(wp:∀v,0<w v){e c κ:ℝ}(paid:A.Pays w e c κ)(en:0≤e)(t:T)(a:V)
    (live:∀U,0<P.eval U)(F:ℝ)(physical:∀U,
      ‖(w a:ℂ)*(((P.eval U:ℂ)⁻¹ • A.density t U).part (C.fire a))‖≤F):
    let g:=fun U=>(w a:ℂ)*originalRaw A t (C.fire a) U
    MemLp g 2 μ ∧ (∫U,‖g U‖^2 ∂μ)≤(F+c)^2*μ.real univ:=by
  intro g
  have cap(U):‖g U‖≤F+c:=restored_singleton_price A wp paid en t U (live U) a F (physical U)
  have sq:MemLp g 2 μ:=MemLp.of_bound (restored_singleton_borel A wp paid.wages en t a).aestronglyMeasurable (F+c) (.of_forall cap)
  refine ⟨sq,?_⟩
  have p:=integral_mono ((memLp_two_iff_integrable_sq_norm sq.1).mp sq) (integrable_const ((F+c)^2))
    (fun U=>pow_le_pow_left₀ (norm_nonneg _) (cap U) 2)
  refine p.trans_eq ?_
  rw [integral_const]
  change μ.real univ*(F+c)^2=(F+c)^2*μ.real univ
  ring

end YM.Integration.FVA1Physical.Exchange.RoseCut
