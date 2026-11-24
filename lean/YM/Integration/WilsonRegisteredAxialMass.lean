import YM.Integration.WilsonRegisteredAxialChart

/-! Global measurable mass and the uniformly available numerical
second-moment charge on the rejected physical collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialMass
open MeasureTheory Filter Lattice RG Wilson Source OPE.Therm RG16 PhysicalNext.Repeat.Legato
open WilsonRegisteredFrozenReading WilsonInheritedRegisteredField Push.Local
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem gross {m N per d:ℕ} (live:m+1 ≤ N) (ref:R.family.ref d ≤ m+1)
    (v:R.family.label d) (o:Site (R.family.side (m+1) per)) (b:ℕ):
    let k:=m+1
    let Z:=packet R.makes live v o
    let L:=R.family.labels.level d
    let f:=previous R live v o b
    Measurable f ∧ ∀U,‖f U‖ ≤ ((A).params k).columns*L.coeffSize (L.core Z.x):=by
  intro k Z L f
  let P:=R.family.path.rep N per k
  let row (i:ℕ) (U:Config G (R.family.side k per)):=
    if coverNumber P.p.B (Z.support i)<b then Z.maskedTerm P i U else 0
  have prior:=WilsonTranslatedFactory.based R.makes ref live o ((R.family.factory d N per).terminal.symm v)
  have fmt:Z.Format o R.family.params P:=prior.1
  obtain ⟨a,c,_,c0,total,_,⟨e,charge,smooth⟩,_⟩:=prior.2
  constructor
  · apply Measurable.tsum (f:=row)
    intro i
    by_cases buy:coverNumber P.p.B (Z.support i)<b
    · simp only [row,buy,if_true]
      exact masked_measurable _ _ (Z.regular i) (fmt.smooth i).borel
    simp only [row,buy,if_false]
    exact measurable_const
  intro U
  have point (i:ℕ):‖row i U‖ ≤ P.p.mass (Z.support i) (e i):=by
    have issued:P.p.supBounds o (Z.support i) (Z.regular i) (e i):=smooth i
    by_cases buy:coverNumber P.p.B (Z.support i)<b
    · rw [show row i U=Z.maskedTerm P i U from if_pos buy]
      apply le_trans _ (P.p.loMass _ _ issued.1)
      by_cases clean:Healthy P.p.threshold (Z.support i) U
      · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ clean]
        exact issued.2 U clean [] (Nat.zero_le _) (by simp)
      rw [Coefficient.maskedTerm,masked_ne _ _ _ _ clean,norm_zero]
      exact issued.1
    rw [show row i U=0 from if_neg buy,norm_zero]
    exact charge.1 i
  have sum:=sumBudget_mono charge (fun i=>norm_nonneg (row i U)) point le_rfl
  exact ((norm_tsum_le_tsum_norm sum.2.1).trans sum.2.2).trans ((le_add_of_nonneg_right c0).trans total)

theorem capacity (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m)) (d:ℕ):
    ∀ᶠ m:ℕ in atTop,let k:=m+1
    (((A).params k).columns*(Real.log (β k))^d)^2 ≤ β k:=by
  have grow:=Next.Rank.Station.hat_rate (A) simple
  have small:=(Real.isLittleO_pow_log_id_atTop (n:=2*(d+1))).bound (by norm_num : 0<(4:ℝ)⁻¹)
  filter_upwards [WilsonRegisteredLogFare.column R simple slow,(tendsto_add_atTop_nat 1).eventually (grow.eventually small)] with m cols price
  intro k
  let s:=Real.log (β k)
  have s0:0 ≤ s:=Real.log_nonneg ((A).fits.delayed k).le
  have c0:0 ≤ ((A).params k).columns:=zero_le_one.trans ((A).params k).columns_ge
  have bp:0 ≤ β k:=zero_le_one.trans ((A).fits.delayed k).le
  have cash:s^(2*(d+1)) ≤ (4:ℝ)⁻¹*(β k):=by
    change ‖s^(2*(d+1))‖ ≤ (4:ℝ)⁻¹*‖β k‖ at price
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg s0 _),abs_of_nonneg bp] using price
  calc
    _ ≤ ((2*s)*s^d)^2:=pow_le_pow_left₀ (mul_nonneg c0 (pow_nonneg s0 d)) (mul_le_mul_of_nonneg_right cols (pow_nonneg s0 d)) 2
    _ = 4*s^(2*(d+1)):=by rw [Nat.mul_comm 2 (d+1),pow_mul,pow_succ];ring
    _ ≤ β k:=by linarith only [cash]

end YM.Integration.WilsonRegisteredAxialMass
end
