import YM.Integration.WilsonMatrixTicketLanesReportedSpatial

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedFees
open Filter Function Real OPE Wilson Pert.Asymptotics
open RGComparison.Core16.Astage PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple)

/-- The signed coefficient of the genuine submitted row, after its engineering rescaling. -/
def entry (d m N p : ℕ) (r : ℝ) (v : R.family.label d) (j : (R.family.labels.level d).Index) : ℂ :=
  ((r : ℂ)^d)⁻¹ * ((R.family.labels.level d).scaled (R.family.path.levels.clock.threshold m)⁻¹
    (((R.family.factory d N p).entries m ((R.family.factory d N p).terminal.symm
      (Axle.root R.makes d m N p v))).x)) j

theorem installed (d m N p : ℕ) (hm : R.family.ref d ≤ m) (hN : m ≤ N) (r : ℝ) (v : R.family.label d)
    (j : (R.family.labels.level d).Index) : entry R d m N p r v j =
    (((R.family.S.a m / r)^d : ℝ) : ℂ) *
    (((regulatorRun R.family N p m)⁻¹ ^ ((R.family.labels.level d).grades j).2 : ℝ) : ℂ) * v j := by
  let F := R.family.labels.level d
  calc
    _ = ((r:ℂ)^d)⁻¹ * (((R.family.S.a m ^ d : ℝ):ℂ) •
        (F.scaled (regulatorRun R.family N p m)⁻¹ v)) j :=
      congrArg (fun z : R.family.label d => ((r:ℂ)^d)⁻¹ * z j)
        (Axle.atCoupling (C:=R.family) (p:=p) R.makes d hm hN v)
    _ = _ := by
      simp only [Pi.smul_apply, smul_eq_mul, Labels.Frame.scaled_apply, Complex.ofReal_pow,Complex.ofReal_div,div_pow]
      ring

include simple in
/-- Every graded angular inverse on the actual upper trajectory is subpower on the spatial clock. -/
theorem inverse {ι : Type} {l : Filter ι} {m : ι → ℕ} (hm : Tendsto m l atTop)
    (N p : ι → ℕ) (hN : ∀ᶠ i in l, m i ≤ N i) (ν : ℕ) :
    RateLE l (ruler R.family m) (fun i => (regulatorRun R.family (N i) (p i) (m i))⁻¹ ^ ν) 0 := by
  let t := ruler R.family m
  let Λ := budgetLog R.family m
  have ratio : Tendsto (fun i => Λ i / t i) l (𝓝 0) := negligible R.family simple hm
  intro c hc
  have B : 0 < c / ((ν:ℝ)+1) := by positivity
  filter_upwards [ratio.eventually (gt_mem_nhds B), (large_s R.family hm).eventually_gt_atTop 0, hN] with i hi ht hN
  have nonnegative : 0 ≤ Λ i := (RG16.Literal.lambda_pos R.family (m i)).le
  have rc := (div_lt_div_iff₀ ht (by positivity : 0 < (ν:ℝ)+1)).mp hi
  have earned := WilsonMatrixTicketLanesReportedCurrency.clock R (m i) (N i) (p i) ν hN
  have ng : 0 ≤ regulatorRun R.family (N i) (p i) (m i) := inv_nonneg.mpr (sqrt_nonneg _)
  calc
    ‖(regulatorRun R.family (N i) (p i) (m i))⁻¹ ^ ν‖ = ((regulatorRun R.family (N i) (p i) (m i))^ν)⁻¹ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr ng) _),inv_pow]
    _ ≤ (exp (-(ν:ℝ)*Λ i))⁻¹ := inv_anti₀ (exp_pos _) earned
    _ = exp ((ν:ℝ)*Λ i) := by rw [←exp_neg]; congr 1; ring
    _ ≤ exp (c*t i) := exp_le_exp.mpr (by nlinarith only [rc,nonnegative])

include simple in
theorem component {ι : Type} {l : Filter ι} {m : ι → ℕ} (hm : Tendsto m l atTop)
    (N p : ι → ℕ) (hN : ∀ᶠ i in l, m i ≤ N i) (r : ι → ℝ) (hr : ∀ᶠ i in l, R.family.S.a (m i) ≤ r i)
    (d : ℕ) (v : ι → R.family.label d) (hv : RateLE l (ruler R.family m) v 0)
    (j : (R.family.labels.level d).Index) :
    RateLE l (ruler R.family m) (fun i => entry R d (m i) (N i) (p i) (r i) (v i) j) 0 := by
  let ν := ((R.family.labels.level d).grades j).2
  refine (((inverse R simple hm N p hN ν).mul hv.norm).mono (by norm_num)).transfer ?_
  filter_upwards [hN,hr,hm.eventually_ge_atTop (R.family.ref d)] with i hN hr hm
  have positive := R.family.S.a_pos (m i)
  have radius := positive.trans_le hr
  have scale : 0 ≤ R.family.S.a (m i) / r i := div_nonneg positive.le radius.le
  have saving : (R.family.S.a (m i) / r i)^d ≤ 1 := pow_le_one₀ scale ((div_le_one radius).2 hr)
  have ng : 0 ≤ regulatorRun R.family (N i) (p i) (m i) := inv_nonneg.mpr (sqrt_nonneg _)
  have coef : 0 ≤ (regulatorRun R.family (N i) (p i) (m i))⁻¹ ^ ν := pow_nonneg (inv_nonneg.mpr ng) _
  rw [installed R d (m i) (N i) (p i) hm hN, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg scale _), Real.norm_eq_abs, abs_of_nonneg coef,
    Real.norm_eq_abs,abs_of_nonneg (mul_nonneg coef (norm_nonneg _))]
  exact mul_le_mul (mul_le_of_le_one_left coef saving) (norm_le_pi_norm (v i) j) (norm_nonneg _) coef

include simple in
/-- The total absolute price of the actual signed heterogeneous marked words, including every graded basis letter.
Each spatial test may choose its upper cutoff and torus period. -/
theorem stencil {ι K I : Type} [Fintype I] {l : Filter ι} {m : ι → ℕ} (hm : Tendsto m l atTop)
    (N p : ι → ℕ) (hN : ∀ᶠ i in l, m i ≤ N i) (r : ι → ℝ) (hr : ∀ᶠ i in l, R.family.S.a (m i) ≤ r i)
    (d : I → ℕ) (v : ∀ j, ι → R.family.label (d j)) (hv : ∀ j, RateLE l (ruler R.family m) (v j) 0)
    (roster : ι → Finset K) (w : ι → K → ℂ)
    (test : RateLE l (ruler R.family m) (fun i => ∑ k ∈ roster i, ‖w i k‖) 0) :
    RateLE l (ruler R.family m) (fun i => ∑ k ∈ roster i,
      ∑ a : ∀ j, (R.family.labels.level (d j)).Index,
        ‖w i k * ∏ j, entry R (d j) (m i) (N i) (p i) (r i) (v j i) (a j)‖) 0 := by
  let t := ruler R.family m
  let e (a : ∀ j, (R.family.labels.level (d j)).Index) (i : ι) :=
    ∏ j, entry R (d j) (m i) (N i) (p i) (r i) (v j i) (a j)
  have word (a : ∀ j, (R.family.labels.level (d j)).Index) : RateLE l t (e a) 0 := by
    simpa [e] using (RateLE.prod (S:=Finset.univ) (r:=fun _ : I => (0:ℝ)) (large_s R.family hm)
      (fun j _ => component R simple hm N p hN r hr (d j) (v j) (hv j) (a j)))
  have all : RateLE l t (fun i => ∑ a, ‖e a i‖) 0 :=
    RateLE.sum (large_s R.family hm) (fun a _ => (word a).norm)
  apply ((test.mul all).mono (by norm_num)).congr
  exact Eventually.of_forall fun i => by
    simp only [Finset.sum_mul, Finset.mul_sum, norm_mul, e]
    exact Finset.sum_comm

end YM.Integration.WilsonMatrixTicketLanesReportedFees
