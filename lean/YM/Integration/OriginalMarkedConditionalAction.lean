import YM.Integration.OriginalMarkedLocalPurchase
import YM.Integration.OriginalMarkedRowPrice

/-! A normalized Haar comparison inside a finite set of moved links with
the same arbitrary exterior configuration in both original physical laws. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedConditionalAction

open Filter Function Lattice RG Wilson MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open OriginalMarkedRunAction OriginalMarkedRowCovariance
open scoped Classical BigOperators

variable {G : Gauge} {n : Side}

def patch (S : Support n) (exterior U : Config G n) : Config G n :=
  fun e => if e.1∈S then U e else exterior e

theorem outside (S : Support n) (exterior U : Config G n) :
    OriginalMarkedLocalDifference.Outside S (patch S exterior U) exterior := by
  intro e h
  exact if_neg h

theorem measurable_patch (S : Support n) (exterior : Config G n) : Measurable (patch S exterior) := by
  apply measurable_pi_lambda
  intro e
  by_cases h : e.1∈S
  · simpa only [patch,h,if_true] using (measurable_pi_apply e : Measurable (fun U : Config G n => U e))
  · simpa only [patch,h,if_false] using (measurable_const : Measurable (fun _ : Config G n => exterior e))

/-- The exterior fixes all complementary links; the unchanged native
product Haar integration independently samples the links based in S. -/
def interior (P : Rep G n) (S : Support n) (exterior : Config G n) (f : Config G n→ℂ) : ℂ :=
  read (prior G n) (fun U => P.eval (patch S exterior U)) (fun U => f (patch S exterior U))

private theorem positive {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {k : X→ℝ} (e : Envelope k) (h : ∀ x,0<k x) : 0<∫ x,k x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (h x).le) (e.integrable μ)).2
  rw [show Function.support k=Set.univ from Set.eq_univ_of_forall fun x => (h x).ne']
  simp

private theorem scaled {X : Type*} [MeasurableSpace X] (μ : Measure X) (c : ℝ) (hc : c≠0)
    (k : X→ℝ) (f : X→ℂ) (hp : 0<∫ x,k x ∂μ) :
    read μ (fun x => c*k x) f=read μ k f := by
  have linear : (∫ x,((c*k x:ℝ):ℂ)*f x ∂μ) = (c:ℂ)*∫ x,(k x:ℂ)*f x ∂μ := by
    simp only [Complex.ofReal_mul,mul_assoc]
    exact integral_const_mul ..
  unfold OriginalMarkedRowCovariance.read
  rw [linear,integral_const_mul,Complex.ofReal_mul]
  field_simp [Complex.ofReal_ne_zero.mpr hc,Complex.ofReal_ne_zero.mpr hp.ne']

variable (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "Ω" => Config G (R.family.side m p)
local notation "dst" => R.family.path.rep N p m
local notation "kept" => approximation R (p:=p) hm d
local notation "omitted" => remainder R (p:=p) hm d
local notation "point" => R.alloy.B.a.budget m
local notation "ε" => (Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N p (m+1))^(d+1)

/-- The same normalized comparison for any measurable parameterization of a
whole physical block with its specified exterior and probability reference. -/
theorem fiber {X : Type*} [MeasurableSpace X] [Nonempty X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p)) (exterior : Ω)
    (ξ : X→Ω) (mx : Measurable ξ) (fixed : ∀ U,OriginalMarkedLocalDifference.Outside S (ξ U) exterior)
    (f : Ω→ℂ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (cap : ∀ U,‖f U‖≤M) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
    ‖read μ (fun U => (dst).eval (ξ U)) (fun U => f (ξ U)) -
      read μ (fun U => (kept).eval (ξ U)) (fun U => f (ξ U))‖ ≤ 2*Real.exp (2*a)*a*M := by
  let g (U : X) := (kept).eval (ξ U)
  let ref := (omitted).additive point exterior
  let u (U : X) := (omitted).additive point (ξ U)
  let c := Real.exp (-ref)
  let k (U : X) := c*g U
  let z (U : X) := Real.exp (-(u U-ref))
  let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
  let F (U : X) := f (ξ U)
  obtain ⟨C,hC⟩ := (OriginalMarkedRunCovariance.keep_envelope R hm A).cost
  have eg : Envelope g := ⟨(OriginalMarkedRunCovariance.keep_envelope R hm A).meas.comp mx,C,fun U => hC (ξ U)⟩
  have hg (U : X) : 0<g U := OriginalMarkedRunCovariance.keep_positive R hm A (ξ U)
  have hc : 0<c := Real.exp_pos _
  have ek : Envelope k := (Envelope.const c).mul eg
  have hk (U : X) : 0<k U := mul_pos hc (hg U)
  have mu : Measurable u := (Activities.E_measurable A.posterior.cut.regular).comp mx
  have mz : Measurable z := Real.measurable_exp.comp (mu.sub measurable_const).neg
  have bound (U : X) : |u U-ref|≤a :=
    OriginalMarkedLocalDifference.variation (omitted) point A.posterior.cut.regular A.posterior.cut.boundE
      (OriginalMarkedLocalPurchase.width R.alloy.B.a) (OriginalMarkedLocalPurchase.width_pays R.alloy.B.a m)
      S (ξ U) exterior (fixed U)
  have ha : 0≤a := (abs_nonneg _).trans (bound (Classical.choice (inferInstance : Nonempty X)))
  have lo (U : X) : Real.exp (-a)≤z U := Real.exp_le_exp.mpr (neg_le_neg (abs_le.mp (bound U)).2)
  have hi (U : X) : z U≤Real.exp a := by
    apply Real.exp_le_exp.mpr
    have lower := (abs_le.mp (bound U)).1
    linarith only [lower]
  have actual : (fun U : X => (dst).eval (ξ U))=k*z := by
    funext U
    have e : Real.exp (-ref)*Real.exp (-(u U-ref))=Real.exp (-(u U)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [OriginalMarkedRunCovariance.factor R hm A (ξ U)]
    change g U*Real.exp (-(u U))=(c*g U)*z U
    rw [←e]
    change g U*(c*z U)=(c*g U)*z U
    ring
  have same : read μ k F=read μ g F := scaled μ c hc.ne' g F (positive μ eg hg)
  have rc := OriginalMarkedRowPrice.normalized_tilt μ ek (fun U => (hk U).le) (positive μ ek hk) mz
    a ha lo hi F (hf.comp mx) M hM (fun U => cap (ξ U))
  change ‖read μ (fun U : X => (dst).eval (ξ U)) F-read μ g F‖≤2*Real.exp (2*a)*a*M
  rw [actual,←same]
  exact rc

/-- Every inherited ordinary and hard activity is integrated on each side.
The actual marginal of the exterior is not used in this conditional estimate. -/
theorem physical (A : Comparison R (p:=p) hm d) (S : Support (R.family.side m p))
    (exterior : Ω) (f : Ω→ℂ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (cap : ∀ U,‖f U‖≤M) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ε
    ‖interior (dst) S exterior f-interior (kept) S exterior f‖ ≤ 2*Real.exp (2*a)*a*M :=
  fiber R hm (prior G (R.family.side m p)) A S exterior (patch S exterior)
    (measurable_patch S exterior) (outside S exterior) f hf M hM cap

end YM.Integration.OriginalMarkedConditionalAction
