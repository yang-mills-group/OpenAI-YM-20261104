import YM.Comparison.RG02.Bulk.Square
import YM.Comparison.RG02.Assembly.Shift
/-!
# Data legend for one independent Fk step before adjacent coupling conversion

`Kernel` not number-of-insertions specific. Works any finite order and period, order/coupling
 not built into Kernel. Path is classical+loop *frozen as function* of Wilson group (and cutoff &
 levels) from the Wilson prescription. `Colors` supplies the t-valued (t expansion coupling g)
 supplementary terms as actual germ functions, with own marker subsets (physical duplicates fine).
 Permits field-independent marks and arbitrary separation geometry already represented, no Vol constraint apart from Envelope
 each entry for global meas/integrab. Each term continuous enough at flat in link-log coordinates;
 no *other representation* can silently be plugged in. Gauge Fk at vacuum uses representative
 tree links, no tree det postulated. Note this contract includes ***no tuning claim***. Need
 histories selected ON that same schedule to use it at multiple steps. `ρ` is witness of
 already defined Critical, hence unique on germ through existing station_unique; user can also
 calculate slope by linear solve on `hessian`. The Fk field coordinates for output V free of any
 constraint here (just represent(g·B)).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bulk
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange
open PertExtension.Series
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} (S : StepData c f) (p : Clip) (P : PathData G)
    (O : ChartRatio G)

/-- A single kernel step of the independent `Kin` prescription (one level, any physical period).
    Later specialize it via BudgetPoint and `Planned`. Here quantify using no budget estimates,
    always at the indicated period (an all-order real tangent identity). No estimates on uniformity
    of the germs. `Gauge.Simple` only when needing the construction. -/
structure Kernel where
  b (F : Forest S.ratio) : fieldDir G c 1 → AxisChart G F
  ratio : LocalRatio O
  branches : S.patch.Branches S.kernel G
  critical : ∀ (F : Forest S.ratio), Critical F p P (b F)
  bounds : ∃ a A Λ, P.Bounds p a A Λ
  gap : ∀ (F : Forest S.ratio), ∃ η : ℝ, 0<η ∧ PriceGap F p P η

variable {S p P O} (K : Kernel S p P O)
-- accessors
namespace Kernel
abbrev group (_ : Kernel S p P O) := G
abbrev tree (_ : Kernel S p P O) := Forest S.ratio
abbrev tag (_ : Kernel S p P O) := S.Choices
abbrev jacobian (_ : Kernel S p P O):= O

variable (F : Forest S.ratio) (t : S.Choices)
include K in
lemma hessian_pos : (hessian F t p P 0 0).PosDef := by
   obtain ⟨η,hp,ha⟩:=K.gap F
   exact surface_pos S p P F t (K.b F) (K.critical F) hp ha

def covariance (_ : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) := (hessian F t p P 0 0)⁻¹
lemma positive : (K.covariance F t).PosDef := (hessian_pos K F t).inv
lemma symm : (K.covariance F t).IsSymm := Matrix.isHermitian_iff_isSymm.mp (K.positive F t).isHermitian
lemma convention (t' : S.Choices) : K.covariance F t = K.covariance F t' := by unfold covariance; rw [hessian_tag S p P F t' K.branches t]

lemma force_square (x : fieldDir G c 1) (v : Precision.Key F G → ℝ) :
    Assembly.jet (Surface S p P F t) 2 (shiftedDir S F (K.b F) x (tape v)) =
      infrared S p P F t (K.b F) x + Gaussian.force (K.covariance F t) v/2 := by
   rw [flat_square .., hessian_force S p P F t (K.hessian_pos F t) v]; rfl
   exact K.critical F
end Kernel

open YM.Multi YM.Marker
open YM.Comparison.RG02.Assembly (GradeAt)

/- `vac` and mark(V) RHS are gauge-invariant input generator germs (along g). Record 
     normalized stage scalars (`v` etc.) separately *before* this, main and loop unaltered. Need additional
     HERE full-group finite-regulator Envelope for convenience to integrate/cut these germs (can
     choose any suitable extension paying costs; never identified with arbitrary full actual input
     to mathematical construction without theorem). No assumption their coefficients match anything
     in the output. GradeAt 3 vac input instead of 5 allows more general consumers; for standard
     accounting only GradeAt >=5 should be used. No dropping finite-dimensional zeromodes in F,
     coarse parameter x external. Probe valuation allowance explicitly supplied. -/

variable {V : Type} [DecidableEq V] (R : Census V)

def projected {Y : Type*} (z : ℝ → Config G f → Y) (x : ℝ × fieldDir G f 1) := z x.1 (represent x.2)

structure Colors (G : Gauge) (f : Side) where
  vac : ℝ→Config G f→ℝ
  mark : Hot R→ℝ→Config G f→ℂ
  power : Hot R→ℕ

variable {R}
structure Well (W : Colors R G f) : Prop where
  suppose_vac : GradeAt 3 (projected W.vac)
  suppose_mark : ∀ i,GradeAt (W.power i) (projected (W.mark i))
  natural : ∀ t : ℝ, GaugeInvariant (W.vac t)
  gauges : ∀ i t, GaugeInvariant (W.mark i t)
  envelope : ∀ t, Envelope (W.vac t)
  prices : ∀ i t, Envelope (W.mark i t)

namespace Colors
/-- Extra vacuum starts at *fluctuation grade* >=3 (`g⁻² * W.vac`). -/
def Standard (W : Colors R G f) := Well W ∧ GradeAt 5 (projected W.vac)
variable (G f R) in
def noHole : Colors R G f := {vac:=0,mark:=0,power:=0}

lemma no_hole (G f R): Standard (noHole (V:=V) G f R) := by
  refine ⟨⟨?_ ,?_ ,fun _ _ _=>rfl,fun _ _ _ _=>rfl, fun x=> Envelope.const 0, ?_⟩,?_⟩
  · exact GradeAt.grade_zero _
  · intro i; exact GradeAt.grade_zero _
  · intro i x; exact ⟨measurable_const,‖(0:ℂ)‖, fun _=>le_rfl⟩
  exact GradeAt.grade_zero _
end Colors

section chart
variable (S) (F : Forest S.ratio)
abbrev Joint := ℝ × SliceDir S F G
private def recast (x : Joint S (G:=G) F) := (x.1,Work.F03.axisLog F x.2)
def posed {Y : Type*} (z : ℝ → Config G f → Y) (x : Joint S (G:=G) F) := z x.1 (Work.F03.live F x.2)
private lemma recast_home : recast S (G:=G) F 0=0 := Prod.ext rfl (show Work.F03.axisLog F (0:SliceDir S F G)=0 from congrArg Prod.snd (Work.F03.inclusion_zero F))
private lemma recast_smooth : ContDiffAt ℝ ω (recast S F (G:=G)) 0 :=
  contDiffAt_fst.prodMk ((show ContDiffAt ℝ ω (Work.F03.axisLog F (G:=G)) 0 from (Work.F03.inclusion_smooth F).snd).comp (0:Joint S F) contDiffAt_snd)
lemma joint_receipt {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {z : ℝ → Config G f → Y} {k : ℕ} (h : GradeAt k (projected z)) : GradeAt k (posed S F z) := by
  apply (GradeAt.coarse h (recast_smooth S F) (recast_home S F)).depends
  have hx := continuous_snd.tendsto (0:Joint S F (G:=G)); filter_upwards [hx.eventually (Work.F03.inclusion_works F)] with y he
  exact congrArg (z y.1) he

variable (W : Colors R G f)
def markFn (i : Hot R) : Joint S F (G:=G) →ℂ:= posed S F (W.mark i)
def supplement (x : Joint S F (G:=G)) := posed S F W.vac x
end chart

end YM.Comparison.RG02.Bulk
