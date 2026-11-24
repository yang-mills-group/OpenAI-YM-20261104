import YM.Pert.Kinetic.SlowMode
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side} {G : Gauge} {p : Clip} {σ C m Λ : ℝ} {R : PathData G} (hb : R.Bounds p σ C Λ) {a : fieldDir G n 1} (h : Slow a m)
include hb h
lemma zero_metric (x : Site n) : (∑ y:PlaqAxes,(p.direct*‖faceCurl (x,y) a‖^2 + ‖holdRow (a:=a) (R:=R) (x,y)‖^2))= ∑ y:PlaqAxes, ‖faceCurl (x,y) a‖^2 := by
   let v (y:PlaqAxes):= faceCurl (x,y) a
   have ht(y:PlaqAxes): ‖holdRow (a:=a) (R:=R) (x,y)‖^2 = ∑ i:PlaqAxes,∑ j:PlaqAxes,R.symbol0 y i*R.symbol0 y j* inner ℝ (v i) (v j) := by
      rw [←real_inner_self_eq_norm_sq,hold_form hb h,sum_inner]; apply Finset.sum_congr rfl;intro i _
      rw [inner_sum]; apply Finset.sum_congr rfl;intro j _; rw [inner_smul_left,inner_smul_right,RCLike.conj_to_real];ring
   simp_rw [ht]; rw [Finset.sum_add_distrib]
   rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (y i:PlaqAxes)=> ∑ j,_)]; rw [←Finset.sum_add_distrib]
   apply Finset.sum_congr rfl;intro i _
   rw [Finset.sum_comm]
   have he(j:PlaqAxes): (∑ y:PlaqAxes,R.symbol0 y i*R.symbol0 y j*inner ℝ (v i) (v j))=(if i=j then 1-p.direct else 0)*inner ℝ (v i) (v j) := by
      rw [← Finset.sum_mul]; congr 1; split_ifs <;> (have h0:=hb.metric i j; simp_all only [ite_true,ite_false]; linarith)
   simp_rw [he]
   rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
   · rw [if_pos rfl,real_inner_self_eq_norm_sq]; unfold v; ring
   intro y _ hy; rw [if_neg (Ne.symm hy),zero_mul]
lemma row_squares (x : Site n) : |(∑ y:PlaqAxes,(p.direct*‖faceCurl (x,y) a‖^2 + ‖ellLine R (x,y) a‖^2))-(∑ y:PlaqAxes, ‖faceCurl (x,y) a‖^2)| ≤ (Fintype.card PlaqAxes:ℝ)*m^3*(2*rowCost σ C) := by
   rw [←zero_metric hb h, ←Finset.sum_sub_distrib]; simp only [add_sub_add_left_eq_sub]
   refine (Finset.abs_sum_le_sum_abs ..).trans ?_
   have he (y : PlaqAxes): |‖ellLine R (x,y) a‖^2 - ‖holdRow (a:=a) (R:=R) (x,y)‖^2| ≤ m^3*(2*rowCost σ C) := by
      let u:=ellLine R (x,y) a; let w := holdRow (a:=a) (R:=R) (x,y)
      rw [sq_sub_sq,abs_mul, mul_comm |‖u‖ + ‖w‖|]; apply (mul_le_mul (d:=C*m+C*m) ((abs_norm_sub_norm_le ..).trans (holds_tilt hb h _)) ?_ (abs_nonneg _) (by have hw:=holds_bound hb h (x,y); have hc:0≤C := tsum_nonneg (hb.rows y).1 |>.trans (hb.rows y).2.2; have hs:=hb.width; positivity)).trans_eq (by unfold rowCost; ring)
      simpa only [abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg w))] using (add_le_add (true_bound hb h _) (holds_bound hb h _)) -- with 2*m maybe
   apply (Finset.sum_le_sum (fun i _=>he i)).trans_eq
   simp [nsmul_eq_mul]; ring
end YM.Pert.Kinetic
