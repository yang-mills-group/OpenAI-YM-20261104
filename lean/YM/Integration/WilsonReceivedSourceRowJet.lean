import YM.Integration.WilsonFirstReceivedIssuedRowTaylor
import YM.Integration.WilsonPhysicalMarkedDefectRowCoefficients

/-! A funded path Taylor expansion with the Laurent coefficients filed by the independent step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedSourceRowJet
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry QuadraticLocal.Sunrise
open Exterior Stationary Comparison.RG02 WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open WilsonFirstReceivedIssuedRowTaylor
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {V X : Type} [DecidableEq V] {G : Gauge} {n : Side} {P : Passport n V} {Γ : Census V}

private theorem sumJet {ι : Type} [Fintype ι] (c : ι → ℂ) (f : ι → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ ω (f i)) (d : ℕ) (t : ℝ) :
    jet (fun z => ∑ i, c i*f i z) d t = ∑ i, c i * jet (f i) d t := by
  unfold jet
  simp only [mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have smooth (i : ι) : ContDiffAt ℝ j (f i) 0 := ((hf i).of_le le_top).contDiffAt
  rw [iteratedDeriv_fun_sum (fun i _ => contDiffAt_const.mul (smooth i)),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := iteratedDeriv_const_smul (smooth i) (c i)
  change iteratedDeriv j (fun z=>c i*f i z) 0 = c i * iteratedDeriv j (f i) 0 at h
  rw [h]
  simp only [Complex.real_smul]
  ring

private theorem field (A : Link G n) (z : ℝ) :
    Stationary.input G n (z • A) = WilsonMeasuredPathTaylor.field (collect G (arm G n 1 A)) z := by
  rw [Stationary.input,map_smul]
  simpa only [Integral.sample,one_smul,one_mul] using WilsonFirstReceivedIssuedRowTaylor.sample (arm G n 1 A) 1 z

private theorem physicalJet (T : Row P Γ G X) (x : X) (A : Link G n) (d : ℕ) (t : ℝ) :
    let f := fun z : ℝ => T.nominal 1 x (Stationary.input G n (z • A))
    jet f d t = T.paint x * polynomial T.atom T.center (collect G (arm G n 1 A)) d t := by
  let v := collect G (arm G n 1 A)
  let words := fun b : Fin T.lamp.r → G.ColorIndex => read v T.center (letters T.atom b)
  intro f
  have same : f = fun z => ∑ b, (T.paint x * (T.atom.coeff b : ℂ))*words b z := by
    funext z
    simp only [f,Row.nominal,Row.grain,one_zpow,one_mul,Pi.smul_apply,smul_eq_mul,field,
      FundedCurvatureRayTaylor.evaluated,mul_sum,v,words,mul_assoc]
  rw [same,sumJet _ words (fun _ => read_smooth ..)]
  simp only [polynomial,mul_sum,v,words,mul_assoc]

theorem filed (T : Row P Γ G X) (x : X) (A : Link G n) (p : ℕ) (he : T.lamp.e ≤ p)
    {g : ℝ} (gp : 0 < g) :
    approximation T g x (collect G (arm G n 1 A)) (p-T.lamp.e+T.lamp.r) g =
      ∑ j ∈ range (p+1), (g:ℂ)^j * (T.paint x * (T.markReceipt j A : ℂ)) := by
  let d := p-T.lamp.e+T.lamp.r
  let f := fun z : ℝ => T.nominal 1 x (Stationary.input G n (z • A))
  let F := QuadraticLocal.Poetry.Helmet.frame T.atom T.center
  have coeffs : jet f d g = T.paint x * (∑ j ∈ range (d+1),g^j * PertExtension.Series.Radial.jet F j A : ℝ) := by
    unfold jet
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [mul_comm ((j.factorial:ℝ)⁻¹),mul_smul,WilsonPhysicalMarkedDefect.RowCoefficients.coefficient]
    simp only [Complex.real_smul,Complex.ofReal_pow]
    ring
  have same := (physicalJet T x A d g).symm.trans coeffs
  have shift := WilsonPhysicalMarkedDefect.RowCoefficients.named T A he g gp
  calc
    _ = (g^T.lamp.lag:ℝ) • (T.paint x * polynomial T.atom T.center (collect G (arm G n 1 A)) d g) := by
      simp only [approximation,Complex.real_smul,d]
      ring
    _ = T.paint x * (g^T.lamp.lag * (∑ j ∈ range (d+1),g^j * PertExtension.Series.Radial.jet F j A) : ℝ) := by
      rw [same,Complex.real_smul,Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [shift]
      push_cast
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring


private theorem lengthBill {r : ℕ} (atom : Atom G r) {σ A : ℝ} (hp : 0 < σ)
    (ha : 0 ≤ A) (rich : atom.budget σ ≤ 1) (j : ℕ) :
    atom.magnitude * ((2*(atom.length:ℝ)*A)^j / j.factorial) ≤ (2*A/σ)^j := by
  have mag : 0 ≤ atom.magnitude := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have factor : 2*(atom.length:ℝ)*A = (2*A/σ)*(σ*atom.length) := by field_simp
  have expo := Real.pow_div_factorial_le_exp (σ*atom.length) (by positivity) j
  rw [factor,mul_pow]
  calc
    _ = (2*A/σ)^j * (atom.magnitude*((σ*atom.length)^j / j.factorial)) := by ring
    _ ≤ (2*A/σ)^j * (atom.magnitude*Real.exp (σ*atom.length)) :=
       mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left expo mag) (by positivity)
    _ ≤ _ := mul_le_of_le_one_right (by positivity) rich

theorem priced (T : Row P Γ G X) (paid : T.Budget) {σ : ℝ} (hs : 0 < σ)
    (rich : T.Graceful σ) (x : X) (A : Link G n) {cap : ℝ} (hc : 0 ≤ cap)
    (axis : ∀ e, ‖collect G (arm G n 1 A) e‖ ≤ cap) (p : ℕ) (he : T.lamp.e ≤ p)
    {g : ℝ} (gp : 0 < g) :
    ‖T.nominal g x (Integral.sample g (arm G n 1 A)) -
      ∑ j ∈ range (p+1), (g:ℂ)^j * (T.paint x * (T.markReceipt j A : ℂ))‖ ≤
      T.salary * (2*(G.colorScale*cap)/σ)^(p-T.lamp.e+T.lamp.r+1) * g^(p+1) := by
  let d := p-T.lamp.e+T.lamp.r
  let v := collect G (arm G n 1 A)
  let c := G.colorScale*cap
  have pos : 0 ≤ c := mul_nonneg G.colorScale_pos.le hc
  have avail : Available T.atom T.center v c := by
    intro _ e _
    rw [speed,G.colorMat_norm]
    exact mul_le_mul_of_nonneg_left (axis e) G.colorScale_pos.le
  have expo : (g^T.lamp.lag)*g^(d+1)=g^(p+1) := by
    rw [←zpow_natCast g (d+1),←zpow_add₀ gp.ne',←zpow_natCast g (p+1)]
    congr 1
    dsimp [d,Loan.lag]
    omega
  have money := WilsonFirstReceivedIssuedRowTaylor.original T paid g x v pos avail d g
  have sample : Integral.sample g (arm G n 1 A) = WilsonMeasuredPathTaylor.field v g := by
    simpa only [one_smul,mul_one] using WilsonFirstReceivedIssuedRowTaylor.sample (arm G n 1 A) g 1
  rw [sample,← filed T x A p he gp]
  have curb := lengthBill T.atom hs pos rich (d+1)
  calc
    _ ≤ T.salary * |g ^ T.lamp.lag| * (T.atom.magnitude * bill T.atom.length c d g) := money
    _ = T.salary*(T.atom.magnitude*((2*(T.atom.length:ℝ)*c)^(d+1)/(d+1).factorial))*
          ((g^T.lamp.lag)*g^(d+1)) := by
        rw [abs_of_pos (zpow_pos gp _),bill,abs_of_pos gp]
        ring
    _ ≤ _ := by
      rw [expo]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left curb T.sound.le) (pow_nonneg gp.le _)

end YM.Integration.WilsonReceivedSourceRowJet
