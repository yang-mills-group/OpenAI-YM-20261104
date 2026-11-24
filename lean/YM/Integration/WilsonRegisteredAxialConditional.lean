import YM.Integration.WilsonRegisteredJointAxial
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! The retained field and its fine field share the original Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialConditional
open MeasureTheory ProbabilityTheory Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonReportingForestAngularReflection WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical Topology ENNReal

variable {G:Gauge} (C:Family G)

theorem conditional {N per m:ℕ} (made:C.Makes) (live:m<N)
    (X:Config G (C.side m per) × Config G (C.side (m+1) per) → ℂ)
    (hX:Integrable X (WilsonRegisteredJointAxial.law C N per m)):
    (∫V,‖actualAverage C (N:=N) (fun U=>X (V,U)) V‖ ∂scene C.path N per m) ≤
      ∫w,‖X w‖ ∂WilsonRegisteredJointAxial.law C N per m:=by
  let μ:=scene C.path N per m
  let K:=QLocalPhysicalPathKernel.next C N per m
  letI:IsProbabilityMeasure μ:=probability made.wilson live.le
  letI:IsFiniteMeasure μ:=⟨by rw [measure_univ];norm_num⟩
  letI:SigmaFinite μ:=IsFiniteMeasure.toSigmaFinite _
  letI:SFinite μ:=inferInstance
  letI:IsMarkovKernel K:=QLocalPhysicalPathKernel.isMarkov C made live
  change Integrable X (μ ⊗ₘ K) at hX
  have rows:Integrable (fun V=>∫U,‖X (V,U)‖ ∂K V) μ:=
    ((Measure.integrable_compProd_iff hX.aestronglyMeasurable).mp hX).2
  have read (V): (∫U,X (V,U) ∂K V)=actualAverage C (N:=N) (fun U=>X (V,U)) V:=by
    rw [show K V=ActualWilsonConditionalRoots.fibre C (N:=N) V from QLocalPhysicalPathKernel.held C made live V]
    exact ActualWilsonConditionalRoots.average C made live V _
  calc
    _ = ∫V,‖∫U,X (V,U) ∂K V‖ ∂μ:=integral_congr_ae (ae_of_all _ fun V=>congrArg norm (read V).symm)
    _ ≤ ∫V,∫U,‖X (V,U)‖ ∂K V ∂μ:=integral_mono_of_nonneg
      (ae_of_all _ fun _=>norm_nonneg _) rows (ae_of_all _ fun _=>norm_integral_le_integral_norm _)
    _ = _ :=(Measure.integral_compProd (μ:=μ) (κ:=K) hX.norm).symm

variable (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem measured (simple:G.Simple) (gate:posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per))
      (H:Config G (R.family.side m per) × Config G (R.family.side (m+1) per) → ℂ),
      let k:=m+1
      let ν:=WilsonRegisteredJointAxial.law R.family N per m
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      let F:=previous R live v o (WilsonDegreeFourInheritedRange.height R p k)
      MemLp H 2 ν →
        (∫V,‖actualAverage R.family (N:=N) (fun U=>H (V,U)*F U) V‖ ∂scene R.family.path N per m)*(Real.log (β k))^t ≤
        Real.sqrt (∫w,‖H w‖^2 ∂ν)*(ε*L.coeffSize (L.core Z.x)):=by
  filter_upwards [WilsonRegisteredJointAxial.measured R simple gate slow J clear a p base t he] with m invoice
  intro N per live d ref v o H k ν Z L F hH
  have q:=invoice N per live d ref v o H hH
  have j:=conditional R.family R.makes live (fun w=>H w*F w.2) q.1
  exact (mul_le_mul_of_nonneg_right j (pow_nonneg (Real.log_nonneg ((A).fits.delayed k).le) t)).trans q.2

end YM.Integration.WilsonRegisteredAxialConditional
