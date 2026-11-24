import YM.Integration.WilsonPhysicalHistoryWalletUniformBound

/-! Exact contraction of the actual signed physical hard wallet from its
source date to any earlier date. A fixed power of the purchased birth heat
can be charged at the testing date despite an unbounded number of RG steps. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletHardRate
open Real Function Filter Finset Lattice RG Wilson OPE OPE.Therm
open PhysicalNext.Repeat.Legato FVA1Physical.Wilson
open scoped BigOperators Topology Classical
variable {G : Gauge}

theorem exact_rate (R : Run G) {j u : ℕ} (ju : j≤u) :
    fiberRate R j u = exp (-(2/5:ℝ)*(R.family.S.scale u-R.family.S.scale j)) := by
  induction u,ju using Nat.le_induction with
  | base => simp [fiberRate]
  | succ u hu ih =>
      let b := R.family.S.block u
      have hb : 0 < (b.val:ℝ) := by exact_mod_cast b.pos
      have single : Extra.Histories.Doors.rate b = exp (-(2/5:ℝ)*log (b.val:ℝ)) := by
        unfold Extra.Histories.Doors.rate
        rw [rpow_def_of_pos hb]
        congr 1
        ring
      have step : fiberRate R j (u+1) = fiberRate R j u*Extra.Histories.Doors.rate b :=
        Finset.prod_Ico_succ_top hu _
      rw [step,ih,single,← exp_add,Schedule.scale_succ]
      congr 1
      ring

theorem kappa_cap (R : Run G) (j : ℕ) : Push.Local.kappa R.family.path j ≤ 1 := by
  apply sqrt_le_one.mpr
  apply exp_le_one_iff.mpr
  exact neg_nonpos.mpr (rpow_nonneg (exp_nonneg _) _)

/-- The original 2/5 contraction strictly outruns the relative growth of any
fixed power of the actual heat, uniformly across all later dates. -/
theorem carries (R : Run G) (simple : G.Simple) {D : ℝ} (degree : 0≤D) :
    ∀ᶠ k : ℕ in atTop, ∀ j u, k≤j → j≤u →
      fiberRate R j u*(R.family.path.levels.clock.hatBeta u)^D ≤ (R.family.path.levels.clock.hatBeta j)^D := by
  let H:=R.family.path.levels
  let θ:=H.clock.hatBeta
  have rise : Tendsto θ atTop atTop :=
    tendsto_atTop_add_const_left _ _ (H.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  obtain ⟨K,after⟩ := eventually_atTop.mp (rise.eventually_ge_atTop ((5/2:ℝ)*D*G.slopeConstant))
  refine eventually_atTop.mpr ⟨K,fun k hk j u kj ju=>?_⟩
  have hj : 0<θ j := zero_lt_one.trans (H.fits.delayed j)
  have hu : 0<θ u := zero_lt_one.trans (H.fits.delayed u)
  have Δ : 0 ≤ R.family.S.scale u-R.family.S.scale j := sub_nonneg.mpr ((OPE.scale_mono _).monotone ju)
  have affine : θ u-θ j = G.slopeConstant*(R.family.S.scale u-R.family.S.scale j) := by
    change (_+_*(R.family.S.scale u))-(_+_*(R.family.S.scale j))=_
    ring
  have ratio : log (θ u)-log (θ j) ≤ (θ u-θ j)/θ j := by
    rw [← log_div hu.ne' hj.ne']
    apply (log_le_sub_one_of_pos (div_pos hu hj)).trans_eq
    field_simp
  have fared : D*G.slopeConstant/θ j ≤ (2/5:ℝ) := by
    apply (div_le_iff₀ hj).mpr
    linarith only [after j (hk.trans kj)]
  have force : D*(log (θ u)-log (θ j)) ≤ (2/5:ℝ)*(R.family.S.scale u-R.family.S.scale j) := by
    calc
      _ ≤ D*((θ u-θ j)/θ j) := mul_le_mul_of_nonneg_left ratio degree
      _ = (D*G.slopeConstant/θ j)*(R.family.S.scale u-R.family.S.scale j) := by rw [affine];ring
      _ ≤ _ := mul_le_mul_of_nonneg_right fared Δ
  change fiberRate R j u*(θ u)^D ≤ (θ j)^D
  rw [exact_rate R ju,rpow_def_of_pos hu,rpow_def_of_pos hj,← exp_add]
  apply exp_le_exp.mpr
  linarith only [force]

end YM.Integration.WilsonPhysicalHistoryWalletHardRate

