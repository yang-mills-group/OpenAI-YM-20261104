import YM.Integration.WilsonRegisteredAxialPull
import YM.Integration.QLocalPhysicalPathKernel

/-! The common physical law of the held configuration and its finer
configuration with the original running posterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredJointAxial
open MeasureTheory ProbabilityTheory Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonReportingForestAngularReflection WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical Topology ENNReal
variable {G:Gauge} (C:Family G)
def law (N per m:ℕ):Measure (Config G (C.side m per) × Config G (C.side (m+1) per)) :=
  (scene C.path N per m) ⊗ₘ (QLocalPhysicalPathKernel.next C N per m)

theorem fine {N per m:ℕ} (made:C.Makes) (live:m<N):
    MeasurePreserving Prod.snd (law C N per m) (scene C.path N per (m+1)):=by
  letI:IsProbabilityMeasure (scene C.path N per m):=probability made.wilson live.le
  letI:IsFiniteMeasure (scene C.path N per m):=⟨by rw [measure_univ];norm_num⟩
  letI:SigmaFinite (scene C.path N per m):=IsFiniteMeasure.toSigmaFinite _
  letI:SFinite (scene C.path N per m):=inferInstance
  letI:=QLocalPhysicalPathKernel.isMarkov C (p:=per) made live
  exact ⟨measurable_snd,(Measure.snd_compProd (scene C.path N per m) (QLocalPhysicalPathKernel.next C N per m)).trans (QLocalPhysicalPathKernel.marginal C made live)⟩

theorem held {N per m:ℕ} (made:C.Makes) (live:m<N):
    MeasurePreserving Prod.fst (law C N per m) (scene C.path N per m):=by
  letI:IsProbabilityMeasure (scene C.path N per m):=probability made.wilson live.le
  letI:IsFiniteMeasure (scene C.path N per m):=⟨by rw [measure_univ];norm_num⟩
  letI:SigmaFinite (scene C.path N per m):=IsFiniteMeasure.toSigmaFinite _
  letI:SFinite (scene C.path N per m):=inferInstance
  letI:=QLocalPhysicalPathKernel.isMarkov C (p:=per) made live
  exact ⟨measurable_fst,Measure.fst_compProd (scene C.path N per m) (QLocalPhysicalPathKernel.next C N per m)⟩

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
      let ν:=law R.family N per m
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      let F:=previous R live v o (WilsonDegreeFourInheritedRange.height R p k)
      MemLp H 2 ν → Integrable (fun w=>H w*F w.2) ν ∧
        (∫w,‖H w*F w.2‖ ∂ν)*(Real.log (β k))^t ≤
        Real.sqrt (∫w,‖H w‖^2 ∂ν)*(ε*L.coeffSize (L.core Z.x)):=by
  filter_upwards [WilsonRegisteredAxialPull.purchased R simple gate slow J clear a p base t he] with m invoice
  intro N per live d ref v o H k ν Z L F hH
  exact invoice N per live d ref v o ν Prod.snd (fine R.family R.makes live) H hH

end YM.Integration.WilsonRegisteredJointAxial
end
