import YM.Integration.WilsonCenteredHaarReading
import YM.Integration.WilsonNormalizedLocalGibbs
import YM.Integration.WilsonHeldChartAction
import YM.Integration.WilsonHeldOldActionPrice
import YM.Integration.WilsonTwoAgeMeasuredRun

/-! Conditional covariance on the actual frozen Wilson fibre. The retained
and returned actions contribute their own masses in the same Haar integral.
The error is charged only to the two centered physical arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldCenteredCovariance
open Function Filter Set MeasureTheory Real Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonCenteredHaarReading WilsonHeldExteriorLaw OriginalMarkedRunAction
open scoped Topology Classical
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def density (f : X→ℝ) (x : X) := f x / ∫ y,f y ∂μ

def bill (f : X→ℝ) (H : X→ℂ) (δ : ℝ) : ℝ :=
  (exp (2*δ)-exp (-(2*δ)))/(∫ y,f y ∂μ) * ∫ y,f y*‖H y‖ ∂μ

private theorem tested {f : X→ℝ} (finite : Integrable f μ) (H : X→ℂ) (bound : Envelope H) :
    Integrable (fun x=>f x*‖H x‖) μ := by
  obtain ⟨M,cap⟩ := bound.cost
  apply (finite.norm.mul_const M).mono' (finite.aestronglyMeasurable.mul bound.meas.aestronglyMeasurable.norm)
  filter_upwards with x
  change ‖f x*‖H x‖‖ ≤ ‖f x‖*M
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg (H x))]
  exact mul_le_mul_of_nonneg_left (cap x) (abs_nonneg _)

private theorem two {p w : X→ℝ} (pi : Integrable p μ) (wi : Integrable w μ)
    (pp : 0 < ∫ x,p x ∂μ) {δ : ℝ} (de : 0≤δ)
    (range : ∀ᵐ x ∂μ,0≤p x ∧ exp (-δ)*1*p x≤w x ∧ w x≤exp δ*1*p x)
    (A B : X → ℂ) (a : Envelope A) (b : Envelope B) :
    let A' := fun x=>A x-mean μ (density μ p) A
    let B' := fun x=>B x-mean μ (density μ p) B
    ‖cov μ (density μ w) A B - cov μ (density μ p) A B‖ ≤
      bill μ p (fun x=>A' x*B' x) δ+(bill μ p A' δ)*(bill μ p B' δ) := by
  have lower : exp (-δ)*1*(∫ x,p x ∂μ) ≤ ∫ x,w x ∂μ := by
    rw [←integral_const_mul]
    exact integral_mono_ae (pi.const_mul _) wi (range.mono fun x h=>h.2.1)
  have wp : 0< ∫ x,w x ∂μ := lt_of_lt_of_le (mul_pos (mul_pos (exp_pos _) one_pos) pp) lower
  have mass (f : X→ℝ) (pos : 0<∫ x,f x ∂μ) : ∫ z,density μ f z ∂μ=1 := by
    simp only [density,integral_div]; exact div_self pos.ne'
  intro A' B'
  have cap (H : X→ℂ) (bound : Envelope H) :
      ‖∫ z,(density μ w z-density μ p z) • H z ∂μ‖ ≤ bill μ p H δ :=
    WilsonNormalizedLocalGibbs.compare μ one_pos de pi wi pp (tested μ pi H bound) range
  have ea : Envelope A' := centered a _
  have eb : Envelope B' := centered b _
  exact compared μ (wi.div_const _) (pi.div_const _) (mass w wp) (mass p pp) a b
    (cap _ (product ea eb)) (cap _ ea) (cap _ eb)

variable {G : Gauge} (R : Run G) {N per j grade : ℕ} (hi : j+1<N)
local notation "n" => R.family.side (j+1) per
local notation "Q" => R.family.path.rep N per (j+1)
local notation "P" => approximation R (p:=per) hi grade

/-- The measured density is already in ν. Each displayed exponential undoes
the same measured action, leaving, respectively, the full original retained
action and the submitted real exponent under the original one-step kernel. -/
theorem physical (receipt : Comparison R (p:=per) hi grade)
    (frozen : Set (Edge (Site n))) (base : Config G n) (E : Set (Fields G frozenᶜ))
    (V : Config G (R.family.side j per)) (area : 0 < (sheet G frozenᶜ) E)
    (Y : Fields G frozenᶜ→ℝ) (Y₀ : ℝ) (fy : Measurable Y) {δ : ℝ} (d : 0≤δ)
    (A : Config G (R.family.side N per) → ℝ) (B : Config G n → ℂ) :
    let U := patch_links G frozen base
    let ν := WilsonHeldChartAction.law R N per j frozen ((cut G frozen) base).1 E V
    let r := fun z=>log ((Q).eval (U z))-log ((Q).eval base)
    let k := fun z=>log ((P).eval (U z))-log ((P).eval base)
    let p := fun z=>exp (k z-r z)
    let w := fun z=>exp ((Y z-Y₀)-r z)
    let old := fun z=>((actualTransport R.family (N:=N) A hi.le (U z) : ℝ):ℂ)
    let fresh := B ∘ U
    let a := fun z=>old z-mean ν (density ν p) old
    let b := fun z=>fresh z-mean ν (density ν p) fresh
    (∀ᵐ z ∂ν, |k z-(Y z-Y₀)|≤δ) → Envelope old → Envelope fresh →
      ‖cov ν (density ν w) old fresh-cov ν (density ν p) old fresh‖ ≤
        bill ν p (fun z=>a z*b z) δ+(bill ν p a δ)*(bill ν p b δ) := by
  intro U ν r k p w old fresh a b regular ha hb
  letI : IsProbabilityMeasure ν :=
    WilsonHeldChartAction.probability R N per j frozen ((cut G frozen) base).1 E V hi.le area
  have mU : Measurable U := WilsonHeldExteriorLaw.measurable_patch frozen base
  have ek := OriginalMarkedRunCovariance.keep_envelope R hi receipt
  have ep := (Q).envelope (R.makes.wilson.represents N per (j+1) hi.le).good
  have mr : Measurable r := (Real.measurable_log.comp (ep.meas.comp mU)).sub measurable_const
  have mk : Measurable k := (Real.measurable_log.comp (ek.meas.comp mU)).sub measurable_const
  have mw : Measurable w := Real.measurable_exp.comp ((fy.sub measurable_const).sub mr)
  have mp : Measurable p := Real.measurable_exp.comp (mk.sub mr)
  have pos := OriginalMarkedRunCovariance.keep_positive R hi receipt
  have qpos := Multi.AxisShift.chosen_positive (H:=R.family.path) R.makes.wilson (p:=per) hi.le
  obtain ⟨c,hc,floor⟩ := WilsonHeldExteriorLaw.upper_floor R N per j hi.le
  obtain ⟨C,cap⟩ := ek.cost
  let fee := exp (log ((Q).eval base)-log ((P).eval base))
  have raw (z) : p z=fee*((P).eval (U z)/(Q).eval (U z)) := by
    change exp ((log _-log _)-(log _-log _)) = _*_
    rw [show (log ((P).eval (U z))-log ((P).eval base))-(log ((Q).eval (U z))-log ((Q).eval base))=
      (log ((Q).eval base)-log ((P).eval base))+(log ((P).eval (U z))-log ((Q).eval (U z))) by ring,
      exp_add]
    change fee*exp (log ((P).eval (U z))-log ((Q).eval (U z))) = _
    rw [exp_sub,exp_log (pos _),exp_log (qpos _)]
  have pi : Integrable p ν := by
    apply (integrable_const (fee*(C/c))).mono' mp.aestronglyMeasurable
    filter_upwards with z
    rw [show ‖p z‖=p z from abs_of_pos (exp_pos _),raw z]
    exact mul_le_mul_of_nonneg_left (div_le_div₀ ((norm_nonneg _).trans (cap (U z)))
      ((le_abs_self _).trans (cap _)) hc (floor _)) (exp_pos _).le
  have range : ∀ᵐ z ∂ν,0≤p z ∧ exp (-δ)*1*p z ≤ w z ∧ w z≤exp δ*1*p z :=
    regular.mono fun z bound=>by
      simp only [mul_one]
      have pair:=abs_le.mp bound
      refine ⟨(exp_pos _).le,?_,?_⟩
      · change exp (-δ)*exp (k z-r z)≤exp ((Y z-Y₀)-r z)
        rw [←exp_add,exp_le_exp]; linarith only [pair.2]
      · change exp ((Y z-Y₀)-r z)≤exp δ*exp (k z-r z)
        rw [←exp_add,exp_le_exp]; linarith only [pair.1]
  have wi : Integrable w ν := by
    apply (pi.const_mul (exp δ*1)).mono' mw.aestronglyMeasurable
    filter_upwards [range] with z price
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact price.2.2
  have pp : 0 < ∫ z,p z ∂ν := (integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun z=>(exp_pos _).le) pi).2 (by
      simp [Function.support,(exp_pos _).ne'])
  exact two ν pi wi pp d range old fresh ha hb

end YM.Integration.WilsonHeldCenteredCovariance
end
