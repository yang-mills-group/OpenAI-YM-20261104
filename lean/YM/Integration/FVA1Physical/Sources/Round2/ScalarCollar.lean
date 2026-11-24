import YM.Integration.FVA1Physical.Sources.Round2.CenteredEntry

/-! A degree-zero physical entry needs only the marked collar for exterior locality.
Its section polynomial vanishes independently of the footprint used to evaluate it. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset Lattice RG YM.Wilson Source Labels Push Push.Local Push.AbsoluteSums
open LocalLTE.Concourse Push.GridApprox.Attach
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {F:Frame G 0}

theorem scalar_regular_collar (R:Rep G n) (Q:Coefficient F n) (z:Site n) (D:SectionData F)
    {P:Hol G} (shape:Q.Format z P R) {κ cost:ℝ} (fund:Q.remBound z R κ cost)
    (r:ℕ) (U W:Config G n) (agree:Agrees (halo (r*leg R.p.B+8) {z}) U W) :
    ‖Q.exponentialEntry z D R U-Q.exponentialEntry z D R W‖ ≤
      2*Real.exp (-R.p.supportExponent*r)*cost := by
  let E:SectionData F:=⟨∅,0⟩
  have vac:Agrees (inspected (E.footprint z)) U W:=by
    intro e he _
    obtain ⟨w,hw,_⟩:=halo_spec.mp (Next.Scheduling.flag_layer _ he)
    simp [E,SectionData.footprint] at hw
  simpa only [center_entry] using regular_entry_exterior R Q z E shape fund r U W vac agree

end YM.Integration.FVA1Physical.Round2.Curvature
