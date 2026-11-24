import YM.Integration.WilsonRootedNonflatResponse

/-! Original positive conditional integration of signed amplitudes.
The released single old vertex is paid at its own graded tariff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatIncome
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period

theorem spend (V:Config G coarse)(u:Config G fine→ℂ)(hu:Envelope u){fee:ℝ}
    (cost:∀U,‖u U‖≤fee*(P).eval U):
    ‖(Δ).push (P).beta u V/((P₀).eval V:ℂ)‖≤fee:=by
  let S:=Δ
  let dens:=fun U:Config G fine=>S.density (P).beta U V
  have strong:=Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below
  have K:=R.family.path.levels.transition_mass d.level d.period (P).beta
  have iu:=StepData.push_slice K V u (hu.integrableC _)
  have ib:=StepData.push_slice K V (P).eval (strong.safe.integrable _)
  have law:((P₀).eval V)=S.push (P).beta (P).eval V:=
    congrFun (R.makes.wilson.steps d.cutoff d.period d.level d.below).1 V
  have pos:=(Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive V
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,div_le_iff₀ pos,law]
  change ‖∫U,dens U • u U ∂prior G fine‖≤fee*∫U,dens U • (P).eval U ∂prior G fine
  calc
    _≤∫ U,‖dens U • u U‖ ∂prior G fine:=norm_integral_le_integral_norm _
    _≤∫ U,fee*(dens U • (P).eval U) ∂prior G fine:=by
      apply integral_mono iu.norm (ib.const_mul fee)
      intro U
      change ‖dens U • u U‖≤fee*(dens U • (P).eval U)
      rw [norm_smul,Real.norm_of_nonneg (K.positive U V)]
      calc
        _≤dens U*(fee*(P).eval U):=mul_le_mul_of_nonneg_left (cost U) (K.positive U V)
        _=fee*(dens U • (P).eval U):=by rw [smul_eq_mul];ring
    _=_:=integral_const_mul fee _

def tariff (a:PrismA G)(c budget:ℝ):ℝ:=‖c^(a.grade-a.rise)‖*(budget*2^(a.rise+2))

theorem vertex {n:Side}{Z:SeriesA G}{σ budget:ℝ}(hs:0<σ)(paid:Draw Z σ budget)
    (a:PrismA G)(ha:a∈Z)(c:ℝ)(o:Site n)(U:Config G n):
    ‖WilsonRootedNonflatDye.vertex a c o U‖≤tariff a c budget:=by
  rw [WilsonRootedNonflatDye.vertex,norm_mul,norm_neg]
  exact mul_le_mul_of_nonneg_left ((OriginalMarkedRunAction.site_packet a.cells hs (paid.2 a ha).toll o).2 U)
    (norm_nonneg _)

theorem columns (D:Allocation G Δ Θ w)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)
    {Z:SeriesA G}{σ budget:ℝ}(hs:0<σ)(paid:Draw Z σ budget)(a:PrismA G)(ha:a∈Z)
    (o:Site fine)(s:Γ.Mode){fee:ℝ}(cost:∀U,‖Actual.atMark s incoming U‖≤fee*(P).eval U):
    ‖WilsonRootedNonflatPerturbation.weight R d D q V x incoming s/((P₀).eval V:ℂ)‖≤fee ∧
    ‖WilsonRootedNonflatPerturbation.prior R d D q V x a o incoming s/((P₀).eval V:ℂ)‖≤
      tariff a g budget*fee:=by
  have h:=WilsonRootedNonflatDye.source R d D q V x incoming floor hs paid a ha o s
  unfold WilsonRootedNonflatPerturbation.weight WilsonRootedNonflatPerturbation.prior
  rw [h.1,h.2]
  refine ⟨spend R d V _ (floor.safe s) cost,spend R d V _ 
    (((WilsonRootedNonflatDye.guarded hs paid a ha g o).1.ofReal_env).mulC (floor.safe s)) ?_⟩
  intro U
  change ‖(WilsonRootedNonflatDye.vertex a g o U:ℂ)*Actual.atMark s incoming U‖≤_
  rw [norm_mul,Complex.norm_real]
  calc
    _≤tariff a g budget*(fee*(P).eval U):=mul_le_mul (vertex hs paid a ha g o U) (cost U)
      (norm_nonneg _) ((norm_nonneg _).trans (vertex hs paid a ha g o U))
    _=_:=by ring

section analytic
variable [Fintype I]{J:Request I}{A:NumericSchedule R.family J}(F:AnalyticInput J A d)(test:TestSpace J.tests)
local notation "W" => F.colors test

/-- Genuine relative tariffs of the submitted signed source before
pushing the old density. They are valid at every original compact field. -/
theorem issued : ∃fee:Γ.Mode→ℝ,(∀s,0≤fee s) ∧
    (∀s U,‖Actual.atMark s (ManuscriptQLocalActualLog.source R d F test) U‖≤fee s*(P).eval U):=by
  have legal:=F.convention.well test
  have paid:Leaf.All (fun U:Config G fine=>Poly.pass (Integral.markedLog g U (W))):=
    Leaf.sum _ _ (fun i=>Leaf.smul (Leaf.atom _) (Leaf.pow (Integral.leaf_mark g (W) legal) i))
  refine ⟨fun s=>max 0 (paid s).cost.choose,fun _=>le_max_left ..,?_⟩
  intro s U
  have positive:=(Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive U
  change ‖(ManuscriptQLocalActualLog.source R d F test U).part s‖≤_
  rw [ManuscriptQLocalActualLog.source,Poly.part_smul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg positive.le,mul_comm]
  exact mul_le_mul_of_nonneg_right (((paid s).cost.choose_spec U).trans (le_max_right ..)) positive.le
end analytic
end YM.Integration.WilsonRootedNonflatIncome
