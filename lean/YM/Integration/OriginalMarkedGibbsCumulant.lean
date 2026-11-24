import YM.Integration.OriginalMarkedGibbsAction
import YM.Integration.WilsonTagCumulantRate

/-! Normalized joint marked cumulants after one real Gibbs update of the
physical gauge links based in the prescribed finite support. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedGibbsCumulant
open Filter MeasureTheory Lattice Wilson RG Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open OriginalMarkedRunAction OriginalMarkedRunCovariance OriginalMarkedGibbsAction
open SelectedCofactorChamberMarginal
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {J : Census V}

theorem controls (S : Support n) (P : Rep G n) (Penv : Envelope P.eval)
    {floor : ℝ} (good : 0<floor) (low : ∀ U,floor≤P.eval U)
    (f : Config G n→ℂ) (M : ℝ) (cap : ∀ U,‖f U‖≤M) (U : Config G n) :
    row S P 1 U=1 ∧ ‖row S P f U‖≤M := by
  let A := exterior S
  let u := ((cut G A) U).1
  let ξ (y : Fields G Aᶜ) := (cut G A).symm (u,y)
  let μ := sheet G Aᶜ
  let k (y : Fields G Aᶜ) := P.eval (ξ y)
  let z := marginal A P.eval u
  have mx : Measurable ξ := (cut G A).symm.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨c,hc⟩ := Penv.cost
  have ek : Envelope k := ⟨Penv.meas.comp mx,c,fun y => hc (ξ y)⟩
  have hi := ek.integrable μ
  have hp : 0<z := good.trans_le (marginal_lower A Penv low u)
  have kn (y) : 0≤k y := good.le.trans (low (ξ y))
  constructor
  · change z⁻¹ • (∫ y,k y • (1:ℂ) ∂μ)=1
    simp only [Complex.real_smul,mul_one,integral_complex_ofReal,Complex.ofReal_inv]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne')
  · have pay : ‖∫ y,k y • f (ξ y) ∂μ‖≤z*M := by
      change _≤(∫ y,k y ∂μ)*M
      rw [←integral_mul_const]
      apply norm_integral_le_of_norm_le (hi.mul_const M)
      apply ae_of_all
      intro y
      rw [norm_smul,Real.norm_of_nonneg (kn y)]
      exact mul_le_mul_of_nonneg_left (cap (ξ y)) (kn y)
    change ‖z⁻¹ • (∫ y,k y • f (ξ y) ∂μ)‖≤M
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact (mul_le_mul_of_nonneg_left pay (inv_nonneg.mpr hp.le)).trans_eq (by field_simp [hp.ne'])

variable (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "Ω" => Config G (R.family.side m p)
local notation "dst" => R.family.path.rep N p m
local notation "keep" => approximation R (p:=p) hm d
local notation "actual" => ActualRunCoarseReadout.expectation R N p m
local notation "ε" => (Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N p (m+1))^(d+1)

def refill (S : Support (R.family.side m p)) (f : Ω→ℂ) : ℂ := actual (row S (keep) f)

include hm in
private theorem measured_bounds (f : Ω→ℂ) (M : ℝ) (cap : ∀ U,‖f U‖≤M) : ‖actual f‖≤M := by
  obtain ⟨pos,finite,massEq⟩ := ActualCoveredNormalization.same_run_reference R N p m hm.le
  have positive : 0 < mass (dst) := by
    unfold mass
    rw [massEq]
    exact partition_pos _
  rw [actual_mean R hm]
  exact bounded finite (fun U => (pos U).le) positive _ _ cap

theorem refill_controls (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p)) :
    refill R (p:=p) (d:=d) hm S 1=1 ∧
    ∀ (f : Ω→ℂ) (M : ℝ), (∀ U,‖f U‖≤M) → ‖refill R (p:=p) (d:=d) hm S f‖≤M := by
  obtain ⟨c,cp,floor⟩ := retained_floor R hm A
  have E := keep_envelope R hm A
  constructor
  · have one : row S (keep) (1:Ω→ℂ)=1 := funext fun U =>
      (controls S (keep) E cp floor 1 1 (fun _ => by simp) U).1
    unfold refill
    rw [one]
    exact ActualRunCoarseReadout.vacuum_one R N p m hm.le
  · intro f M bound
    exact measured_bounds R hm _ _ (fun U => (controls S (keep) E cp floor f M bound U).2)

/-- Both normalized full physical reads are contractions. This removes the
large-support exponential from the signed cutoff error on every marked test. -/
theorem linear (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p))
    (f : Ω→ℂ) (meas : Measurable f) (M : ℝ) (pos : 0≤M) (cap : ∀ U,‖f U‖≤M) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
    ‖actual f-refill R (p:=p) (d:=d) hm S f‖≤(2*Real.exp 2*a)*M := by
  let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
  have ha : 0≤a := OriginalMarkedLocalPurchase.fee_nonneg _ _ _ (pow_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (IterationFour.Currency.g_pos R.makes N p (m+1) hm).le) _)
  by_cases small : a≤1
  · exact (OriginalMarkedGibbsAction.physical R hm A S f meas M pos cap).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith : 2*a≤2)) (by norm_num)) ha) pos)
  · have big : 1≤a := le_of_not_ge small
    have exp1 : 1≤Real.exp 2 := Real.one_le_exp (by norm_num)
    have pay : 2≤2*Real.exp 2*a :=
      (show (2:ℝ)=2*1*1 by ring).trans_le (mul_le_mul (mul_le_mul_of_nonneg_left exp1 (by norm_num))
        big zero_le_one (by positivity))
    calc
      ‖actual f-refill R (p:=p) (d:=d) hm S f‖≤‖actual f‖+‖refill R (p:=p) (d:=d) hm S f‖ := norm_sub_le .. 
      _ ≤ M+M := add_le_add (measured_bounds R hm f M cap) ((refill_controls R hm A S).2 f M cap)
      _ = 2*M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right pay pos

private theorem compare_marked {X : Type*} [MeasurableSpace X] (s : J.Mode)
    (E L : (X → ℂ) → ℂ) (hE : E 1 = 1) (hL : L 1 = 1)
    (F : V → X → ℂ) (b : V → ℝ) (hmF : ∀ i, Measurable (F i)) (hb : ∀ i, 0 ≤ b i)
    (cap : ∀ i x, ‖F i x‖ ≤ b i) (C : ℝ)
    (eb : ∀ f M, (∀ x, ‖f x‖ ≤ M) → ‖E f‖ ≤ M)
    (lb : ∀ f M, (∀ x, ‖f x‖ ≤ M) → ‖L f‖ ≤ M)
    (compare : ∀ f, Measurable f → ∀ M, 0 ≤ M → (∀ x, ‖f x‖ ≤ M) → ‖E f - L f‖ ≤ C*M) :
    ‖WilsonTagCumulantRate.coefficient s E F - WilsonTagCumulantRate.coefficient s L F‖ ≤
      C * WilsonTagCumulantRate.slope s b := by
  have product (T : Finset V) (x : X) : ‖(∏ i∈T,F i) x‖ ≤ ∏ i∈T,b i := by
    simp only [Finset.prod_apply,norm_prod]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => cap i x)
  have transfer := WilsonTagCumulantRate.transfer (A:=X → ℂ) s E L hE hL F b hb 1 C zero_le_one
    (fun T => eb _ _ (product T)) (fun T => lb _ _ (product T))
    (fun T => by
      rw [one_mul]
      have measurable : Measurable (∏ i∈T,F i) := by
        simpa only [← Finset.prod_apply] using Finset.measurable_fun_prod T (fun i _ => hmF i)
      exact compare (∏ i∈T,F i) measurable (∏ i∈T,b i)
        (Finset.prod_nonneg fun i _ => hb i) (product T))
  simpa only [one_mul] using transfer

/-- Reuse the very same complete normalized exterior law and the same
physical refill for every marked subset and every signed partition. -/
theorem connected (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p)) (s : J.Mode)
    (F : V→Ω→ℂ) (b : V→ℝ) (hmF : ∀ i,Measurable (F i)) (hb : ∀ i,0≤b i)
    (cap : ∀ i U,‖F i U‖≤b i) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
    ‖WilsonTagCumulantRate.coefficient s actual F-
      WilsonTagCumulantRate.coefficient s (refill R (p:=p) (d:=d) hm S) F‖ ≤
      (2*Real.exp 2*a)*WilsonTagCumulantRate.slope s b := by
  have c := refill_controls R hm A S
  exact compare_marked (X:=Ω) s actual (refill R (p:=p) (d:=d) hm S)
    (ActualRunCoarseReadout.vacuum_one R N p m hm.le) c.1 F b hmF hb cap _
    (measured_bounds R hm) c.2 (linear R hm A S)

end YM.Integration.OriginalMarkedGibbsCumulant

