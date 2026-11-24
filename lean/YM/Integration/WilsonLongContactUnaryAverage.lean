import YM.Integration.WilsonLongContactUnaryHousing

/-! The registered one-letter salary on the full original reserve and tag mixture. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.PhysicalNext.Repeat.WilsonLongContactUnaryAverage
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt Brim Next.Foundations AnalyticBridge.LocalGaussianLaws
open YM.Integration.WilsonLongContactTown WilsonLongContactFrozenGaussian
open scoped Topology Classical BigOperators
variable {G : Gauge} {c f L : Side} {S : StepData c f} {R : Rep G f} {T : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ α : ℝ} {o : Target.Order G W}
    (H : Cash W x μ L Q o α T R) (i : ℕ) (M : Leaf R) (key : M.turn=.logKey i)


open PhysicalNext.JointLoad.Heir ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.March WilsonLongContactUnaryHousing Baffle WardBin.Lies

def branch (χ : Chi) (V : Config G c) : ℝ :=
  likely (fun r : Reserve S=>(town T M).grove (prism T x χ o.K V (allot r)) (solitary S M) W o.a Q.table Q.halo)

def oracle (χ κ q : Chi) (b : ℝ) (D : Record) (base V : Config G c) : ℝ :=
  likely (fun r : Reserve S=>likely (fun tag:S.Choices=>
    forecast (Brim.foyer H i (allot r) χ base tag) i (Brim.mapcase H i (allot r)) q κ b D V M.ingredient))

theorem linear {I : Type} [Fintype I] (a b : I→ℝ) :
    likely (fun i=>a i-b i)=likely a-likely b := by
  unfold likely;rw [Finset.sum_sub_distrib,mul_sub]

include key in
theorem paid {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ κ q : Chi) (b : ℝ) (D : Record) (base : Config G c) (V : E → Config G c) (n : ℕ) (v : ℝ)
    (healthy : Healthy (Pressure.temp x) (Brim.plate H i).support base)
    (signed : ∀ (F:Forest S.ratio) (tag:S.Choices),
      let X:=Brim.foyer H i F χ base tag
      Brush n v 1 (fun y=>(town T M).cinema (vary X (V y)) (solitary S M) W o.a Q.table Q.halo
        (podium S G (Brim.plate H i).support (radiusB x))-
        forecast X i (Brim.mapcase H i F) q κ b D (V y) M.ingredient) 0) :
    Brush n v 1 (fun y=>branch (T:=T) (Q:=Q) (W:=W) (x:=x) (o:=o) M χ (V y)-oracle H i M χ κ q b D base (V y)) 0 := by
  classical
  let rfield (F : Forest S.ratio) (tag : S.Choices) (y : E) :=
    (town T M).cinema (vary (Brim.foyer H i F χ base tag) (V y)) (solitary S M) W o.a Q.table Q.halo
        (podium S G (Brim.plate H i).support (radiusB x))
  let model (F : Forest S.ratio) (tag : S.Choices) (y : E) :=
    forecast (Brim.foyer H i F χ base tag) i (Brim.mapcase H i F) q κ b D (V y) M.ingredient
  have sum (F:Forest S.ratio) := March.Captain.avgBrush
    (fun tag y=>rfield F tag y-model F tag y) v 0 (signed F)
  have all:=March.Captain.avgBrush (fun r y=>likely (fun tag=>rfield (allot r) tag y-model (allot r) tag y))
    v 0 (fun r=>sum (allot r))
  convert all using 1
  funext y
  unfold branch oracle
  rw [←linear]
  apply congrArg likely
  funext r
  rw [linear,received H i M key (allot r) χ base (V y) healthy]

end YM.PhysicalNext.Repeat.WilsonLongContactUnaryAverage
