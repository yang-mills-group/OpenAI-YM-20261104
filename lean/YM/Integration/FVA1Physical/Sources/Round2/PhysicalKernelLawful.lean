import YM.Integration.FVA1Physical.Sources.Round2.PhysicalFieldKernel
import YM.ProjectorNext.EQUATION_CAMPAIGN.Receiving

/-! Gauge invariance of the actual normalized inserted posterior for any
admitted incoming representation and any eligible shared-tag kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function MeasureTheory RG Lattice YM.Wilson MSbar MSbar.Bulk MSbar.Mosaic Precision
open RGComparison.Core16 RGComparison.Core16.Spool Push.SectorMeasure.Presented
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

theorem boundaryStencil_invariant (A : Issue G) (o : ι → Site A.f) (part : Bool)
    (branch : A.S.patch.Branches A.S.kernel G) {σ C Λ δ w : ℝ} (law : A.pre.Lawful σ C Λ δ w) :
    GaugeInvariant (boundaryStencil J A o part) := by
  let φ:=fun U=>look part (tally J o U)
  have env : Envelope φ:=⟨((look part).continuous.comp (tally_cont J o)).measurable,_,stencil_bounded J o part⟩
  have dens:=A.pre.envelope law
  have gi:=lawful_gi law
  have total : GaugeInvariant (φ*A.pre.eval) := fun k U=>congrArg₂ (·*·)
    (congrArg (look part) (tally_invariant J o k U)) (gi k U)
  have fine:=ProjectorNext.Equations.Finite.invariant A.S branch A.pre.beta _ total
    ((env.mul dens).integrable _) (fun U W k=>A.S.covary branch ..)
  have vac:=ProjectorNext.Equations.Finite.invariant A.S branch A.pre.beta _ gi
    (dens.integrable _) (fun U W k=>A.S.covary branch ..)
  exact fun k V=>congrArg₂ (·/·) (fine k V) (vac k V)
end YM.Integration.FVA1Physical.Round2.Curvature
