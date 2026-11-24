import YM.Integration.WilsonAddressedEquationAllowance
import YM.Integration.WilsonThermometerEquationReturn

/-! The actual displaced Haar difference at the normalization of its reported label. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedMatchedEquation
open Function Filter Set MeasureTheory Lattice RG Labels Wilson Source Bid Cells Push
open PhysicalNext.Repeat.Legato MergeProof FullVolume Extraction Next.Extract
open Extra.Histories
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {d : ℕ}
local notation "C" => R.family
local notation "F" => R.family.labels.level d
variable {V : ∀ d, SectionData (R.family.labels.level d)} {W : Mark.Weave G}
  {P : ∀ d, (ℕ × ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)}
  {b : Presentation R.family} {ζ : ℕ → ℕ → ℝ}

def bare (P : ∀ d, (ℕ × ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
    (b : Presentation R.family) (N p : ℕ) (x : R.family.label d) :=
  (P d (N,p)).symm ((R.family.factory d N p).terminal.symm (x-b.step d (N,p) x))

theorem coefficients (house : Hearthside R.family V W P b ζ) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, ∀ x : R.family.label d,
      (F).coeffSize (bare R P b N p x) ≤
        2 * Fintype.card (F).Index * ‖x‖ * Real.exp (ε * R.family.S.scale N) := by
  obtain ⟨B,control⟩ := house.uniform d
  obtain ⟨E,Y,stamp⟩ := house.hearth d
  filter_upwards [Work.D01.terminal_ball (C) R.makes d (1+|B|) ε pos, stamp.stamped]
    with N price funded
  intro p x
  let c : ℂ := ‖x‖
  let y := c⁻¹ • x
  have scalar : ‖c‖ = ‖x‖ := Complex.norm_real _ |>.trans (Real.norm_of_nonneg (norm_nonneg _))
  by_cases zero : x=0
  · simp [zero,bare,Frame.coeffSize]
  have nz : c ≠ 0 := by simpa [c] using (norm_ne_zero_iff.mpr zero)
  have unit : ‖y‖ = 1 := by rw [show ‖y‖=‖c⁻¹‖*‖x‖ from norm_smul _ _, norm_inv, scalar, inv_mul_cancel₀ (norm_ne_zero_iff.mpr zero)]
  have norm_proj := ((b.step d (N,p)).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right ((control (N,p)).trans (le_abs_self B)) (norm_nonneg y))
  have inside : ‖y-b.step d (N,p) y‖ ≤ 1+|B| := by
    refine (norm_sub_le _ _).trans ?_
    simpa [unit] using add_le_add_left norm_proj ‖y‖
  let z := (R.family.factory d N p).terminal.symm (y-b.step d (N,p) y)
  have bound : ‖z‖ ≤ Real.exp (ε*R.family.S.scale N) := price p _ inside
  have mass : (F).coeffSize z ≤ Fintype.card (F).Index * Real.exp (ε*R.family.S.scale N) := by
    calc
      _ ≤ ∑ _i:(F).Index,Real.exp (ε*R.family.S.scale N) :=
        Finset.sum_le_sum fun i _ => (norm_le_pi_norm z i).trans bound
      _ = _ := by simp
  have raw := ((funded p).2.1 z).trans (mul_le_mul_of_nonneg_left mass (by norm_num))
  have back : c • y = x := by simp [y,smul_smul,nz]
  have scale : bare R P b N p x = c • bare R P b N p y := by
    calc
      _ = bare R P b N p (c • y) := congrArg _ back.symm
      _ = _ := by simp [bare,←smul_sub]
  rw [scale]
  change ∑ i:(F).Index,‖c • (bare R P b N p y) i‖ ≤ _
  simp_rw [norm_smul,scalar]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left raw (norm_nonneg x)).trans_eq (by ring)

theorem projected {N p : ℕ} (x : R.family.label d) (o : Site (R.family.side N p)) :
    WilsonThermometerEquationReturn.difference R (V d) (fun n q=> P d (n,q)) N p o
      (bare R P b N p x) =
      WilsonOffsetReportingProducts.residual R.family (V d) N p (P d (N,p))
        (x-b.step d (N,p) x) o := by
  change R.family.O N p ((R.family.factory d N p).terminal ((P d (N,p)) (bare R P b N p x))) o -
    initial (V d) R.family.path N p (bare R P b N p x) o = _
  simp [bare,WilsonOffsetReportingProducts.residual,WilsonOffsetEquationLaw.incoming]

theorem original (simple : G.Simple) (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (house : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∃ h : k ≤ N, ∀ p (x : R.family.label d)
      {m : ℕ} (earlier : m ≤ k) (t : Site (R.family.side m p)) (o : Site (R.family.side N p)),
      let T := center R.family.S p (earlier.trans h) 0
      o ∈ T.margin t (3*span R.family.S h p) →
      ∃ H : Config G (R.family.side N p) → ℂ, Interior (T.chamber 0) H ∧
        T.rootTest (R.family.beta N p) H ≤ 2*Fintype.card (F).Index*‖x‖*
          Real.exp (-(1/64:ℝ)*R.family.S.scale N) ∧
        T.copy t H = WilsonOffsetReportingProducts.residual R.family (V d) N p (P d (N,p))
          (x-b.step d (N,p) x) o := by
  filter_upwards [WilsonThermometerEquationReturn.returned R simple portfolio house d] with k dated
  filter_upwards [dated,coefficients R house (1/64) (by norm_num)] with N issued bounded
  obtain ⟨h,heard⟩ := issued
  refine ⟨h,?_⟩
  intro p x m earlier t o T inside
  obtain ⟨H,localH,expense,exactH⟩ := heard p (bare R P b N p x) earlier t o inside
  refine ⟨H,localH,expense.trans ?_,exactH.trans (projected R x o)⟩
  refine (mul_le_mul_of_nonneg_right (bounded p x) (Real.exp_pos _).le).trans_eq ?_
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

end YM.Integration.WilsonAddressedMatchedEquation
