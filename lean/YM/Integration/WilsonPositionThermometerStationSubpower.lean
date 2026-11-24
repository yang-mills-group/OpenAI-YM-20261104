import YM.Integration.WilsonPositionThermometerStationWallet

/-! The coefficient budget of an enrolled station vector is subpower in the
original inverse coupling. The estimate is uniform in the upper cutoff, period
and station at the stated extraction date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationSubpower
open Function Set Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open scoped BigOperators Classical Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {H : (Bel C.book).Hierarchy}

private theorem scales (d : ℕ) {t b : ℝ} (ht : 1 ≤ t) (hb : 1 ≤ b) (w : C.label d) :
    let F := C.labels.level d
    F.coeffSize (F.scaled t (weightTag C d b w)) ≤ t^(Atlas.leash F)*b^d*F.coeffSize w := by
  let F := C.labels.level d
  change (∑ i, ‖F.scaled t (weightTag C d b w) i‖) ≤ _ * (∑ i, ‖w i‖)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have y : (F.grades i).2 ≤ Atlas.leash F := Finset.le_sup (f:=fun k => (F.grades k).2) (mem_univ i)
  change ‖((t^(F.grades i).2 : ℝ) : ℂ) * ((b : ℂ)^(F.grades i).1 * w i)‖ ≤ _
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans ht) _),Real.norm_of_nonneg (zero_le_one.trans hb),
    ←mul_assoc]
  gcongr
  exact F.bound i

private theorem amount (D E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ b : ℝ, b ≤ Perch.y x →
    2*(2*Real.exp ((Perch.y x)^2))^E*(Real.exp ((Perch.y x)^2*b))^D ≤ x^ε := by
  let c : ℝ := 1+2*(E:ℝ)+(D:ℝ)
  have hc : 0<c := by dsimp [c]; positivity
  have slow := (Real.isLittleO_pow_exp_atTop (n:=3)).tendsto_div_nhds_zero
  have bound := (slow.eventually (gt_mem_nhds (div_pos hε hc))).filter_mono (show atTop ≤ atTop by rfl)
  filter_upwards [Perch.y_rate.eventually bound, Perch.y_rate.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ)] with x gap one xpos b cap
  let z := Perch.y x
  have square : 1≤z^2 := by change 1≤(Perch.y x)^2; nlinarith [sq_nonneg (Perch.y x-1)]
  have minor : z^2 ≤ z^3 := by rw [pow_succ]; exact le_mul_of_one_le_right (sq_nonneg _) one
  have two : (2:ℝ) ≤ Real.exp (z^3) :=
    (by linarith [Real.add_one_le_exp (1:ℝ)] : (2:ℝ)≤Real.exp 1).trans (Real.exp_le_exp.mpr (square.trans minor))
  have tall : 2*Real.exp (z^2) ≤ Real.exp (2*z^3) := by
    rw [show 2*z^3=z^3+z^3 by ring, Real.exp_add]
    exact mul_le_mul two (Real.exp_le_exp.mpr minor) (Real.exp_pos _).le (Real.exp_pos _).le
  have weight : Real.exp (z^2*b) ≤ Real.exp (z^3) :=
    Real.exp_le_exp.mpr (by rw [pow_succ]; exact mul_le_mul_of_nonneg_left cap (sq_nonneg _))
  have budget : c*z^3 ≤ Real.exp z * ε := by
    have gap' : z^3 / Real.exp z < ε/c := gap
    have paid := (div_lt_div_iff₀ (Real.exp_pos z) hc).mp gap'
    linarith [paid]
  calc
    _ ≤ Real.exp (z^3) * (Real.exp (2*z^3))^E * (Real.exp (z^3))^D := by gcongr
    _ = Real.exp (c*z^3) := by rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add];congr 1;dsimp [c];ring
    _ ≤ x^ε := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans xpos)]
      apply Real.exp_le_exp.mpr
      have eq : Real.exp z=Real.log x := Real.exp_log (Real.log_pos xpos)
      simpa [eq] using budget

theorem original (smooth : G.Simple) (hC : C.Makes) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ {D : ℕ} (V : Vane C D) (j : Fin (D+1)), j.val=d → V.k=k →
      V.checked f H D → ∀ (w : (Bel C.book).Field j) (N p : ℕ), k < N →
      (C.labels.level j).coeffSize (awake C j k N p (V.wheel.atCut (N,p) j w)) ≤
      (C.path.levels.clock.hatBeta k)^ε * (C.labels.level j).coeffSize (Further.CorrectedLift.ladder C j w) := by
  have price := (Next.Rank.Station.hat_rate C.path.levels smooth).eventually (amount d (Atlas.leash (C.labels.level d)) ε hε)
  filter_upwards [price] with k tariff D V j hj hk ready w N p top
  subst k
  let F := C.labels.level j
  let m := C.path.levels.clock.monitor V.k
  let b := Next.Rank.Station.mag C.path.levels V.b V.k
  have hm : 1 ≤ m := Real.one_le_exp (sq_nonneg _)
  have hb : 1 ≤ b := Real.one_le_rpow hm (by linarith [ready.high.1])
  have reserve := scales (C:=C) j (t:=2*m) (b:=b) (by linarith) hb (Further.CorrectedLift.ladder C j w)
  have tag : b=Real.exp ((Perch.y (C.path.levels.clock.hatBeta V.k))^2*V.b) := Atlas.mag_bill _ _ _
  have T := tariff V.b ready.high.2
  rw [←hj] at T
  change 2*(2*m)^(Atlas.leash F)*(Real.exp ((Perch.y (C.path.levels.clock.hatBeta V.k))^2*V.b))^j.val ≤ _ at T
  rw [←tag] at T
  calc
    _ ≤ WilsonPositionThermometerStationWallet.allowance V j w :=
      WilsonPositionThermometerStationWallet.original V j w hC ready top
    _ ≤ (2*(2*m)^(Atlas.leash F)*b^j.val)*F.coeffSize (Further.CorrectedLift.ladder C j w) := by
      exact (mul_le_mul_of_nonneg_left reserve (zero_le_two)).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_of_nonneg_right T (by unfold Frame.coeffSize; positivity)

end YM.Integration.WilsonPositionThermometerStationSubpower
end
