import YM.Integration.WilsonRetainedOldPlacements
import YM.Integration.WilsonRootedNonflatDye

/-! Gauge invariance applies to each actually filed previous site at
every compact field, including its two inherited curvature paths. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatPreviousSite
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open OriginalMarkedRunAction WilsonLimitConstruction
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}

theorem packet {k:ℕ}(a:ℕ→Atom G k)(hue:∀i,(a i).Invariant)(o:Site n):GaugeInvariant (sitePacket a o):=by
  intro h U
  have coil (s:Signed)(i:ℕ):(a i).unmasked (pull s 0 (gauge h U)) o=(a i).unmasked (pull s 0 U) o:=by
    rw [Work.F05.pull_gauge_zero]
    unfold Atom.unmasked
    simp only [Work.F05.slot_gauge]
    exact hue i ..
  unfold sitePacket
  simp only [coil]

theorem bare {B:Clip}{K:PathData G}{σ c L:ℝ}(paid:K.Bounds B σ c L)(o:Site n):
    GaugeInvariant (secondAt B K o) ∧ GaugeInvariant (interactionAt K o):=by
  constructor
  · intro h U
    have atPull (s:Signed):quadraticAt B K o (pull s 0 (gauge h U))=quadraticAt B K o (pull s 0 U):=by
      rw [Work.F05.pull_gauge_zero]
      simp only [quadraticAt,face_gauge,G.price_conj,Work.F05.ell_gauge paid,G.norm_adjoint]
    unfold secondAt
    simp only [atPull]
  · intro h U
    unfold interactionAt
    rw [packet K.cubic (fun i=>(paid.invariant i).2.1) o h U,packet K.quartic (fun i=>(paid.invariant i).2.2) o h U]

theorem springs (R:Run G)(N per j r:ℕ)(live:j≤N)(Z:SeriesA G){σ c:ℝ}(draw:Draw Z σ c)
    (g:ℝ)(o:Site (R.family.side j per)):
    GaugeInvariant (springAt R N per j r Z g o) ∧
      GaugeInvariant (fun U=>R.alloy.B.kin.alpha N j*secondAt (R.family.path.levels.params j).clip
        (R.family.path.rep N per j).path o U+springAt R N per j r Z g o U):=by
  let t:=R.family.path.levels.params j
  let P:=R.family.path.rep N per j
  have hc:R.family.path.Conv N per j:=R.makes.wilson.represents N per j live
  have hp:P.path.Bounds t.clip t.width t.paths (R.family.path.levels.clock.loopCap j):=by
    dsimp only [t,P]
    rw [←hc.clip]
    exact hc.good.paths
  have core:=bare hp o
  have roster (f:ℝ):GaugeInvariant (springPacketsAt Z f o):=by
    intro h U
    unfold springPacketsAt
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [packet a.cells (fun i=>(draw.2 a ha).hue i) o h U]
  have hspring:GaugeInvariant (springAt R N per j r Z g o):=by
    intro h U
    unfold springAt
    dsimp only
    rw [core.1 h U, core.2 h U,roster _ h U]
  refine ⟨hspring,?_⟩
  intro h U
  dsimp only
  rw [core.1 h U,hspring h U]

end YM.Integration.WilsonRootedNonflatPreviousSite
