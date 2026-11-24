import YM.RGComparison.Core16.Binding
import YM.RGComparison.Core16.Witness.Levy

/-! Construct the stronger Context rather than pick multiple contexts. Entry-level interpretation:
uses UV provider route (UV Case provider, full receipt in Floral, uses true tuned forest Sect and
Mast gate & Cellar), adds simultaneous OPE quota/subpower & Maxwell-measuring supplies to this
very witness. Ledger unchanged; the new stronger existential elaborates to Context and explicitly
exhibits the Pricing hypotheses & geometry condition from the pinned Ledger.
No q-local estimate or sharp estimate in this result. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16
open Filter Function Set Metric Topology Extraction Spec
open Next.UVStress OPE OPE.Levy Table Ward Climb

-- Final choice of proof witnesses for intermediate comparison -- all fields either inherited or
-- produced from the same Family in Assemble; not assuming the UV Bundle alone supplies them.
structure Exhibit (G:Gauge)(hG:G.Simple)(b:ℝ) extends Context G hG b where
    services : OPE.Services C f T
    calendar : Witness.CalendarGate C.path.levels
    mesh : Wcmain C
    R : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin
    X : Scaling T -- weak leading data (not the A frame)
    paths : OPE.Levy.Ticket F R X
    approaches : Approaches (Next.UVStress.path X) (isoPanel X)

variable {G:Gauge} {h:G.Simple} {b:ℝ} (E: Exhibit G h b)
namespace Exhibit

lemma structured : Nesting.Uniform E.F E.R ∧ Orbits.Foundation E.F E.R :=
   ⟨Nesting.uniform E.F E.R E.services, Orbits.produce E.F E.R E.services⟩

/-- Weak TP data, strictly weaker than a qass comparison even at relevant order zero.
Repeat weak extraction and upper bounds feeding physical consumers. All on the same refinement. -/
theorem pickJewel (J:Witness.Rewards G)(hJ:Witness.Encounters J) {P_extra : RG.Levels G→Prop} (h_extra : Witness.Demandable P_extra) (h:G.Simple) {b:ℝ} (hb:0<b) : ∃ e:Exhibit G h b,P_extra e.C.path.levels∧ ∃ V:Hangar e.C h,Witness.permits J V.R:=by
    obtain ⟨C,hB,h_extra0,hRR,hC,H,hS,hU⟩:= OPE.Levy.Core16.simultaneousWith G h_extra J hJ h b hb
    obtain ⟨f,T,U,F,R,X,hT,hR,ha,hD,hE⟩:= hU Extraction.Order.full
    obtain ⟨L,hL⟩:= EveryPhase.all_characters F
    refine ⟨{ C,f := Extraction.Order.full.refine f, T, F, L
              stamped:=hB, floral:=H, fullMesh:= UVExtension.Reports.useFull H ⟨F⟩
              margins:= UVExtension.Poppy.bravo (UVExtension.Oasis.appears H)
              services:=U, mesh:=hC, completed:=hL, calendar:=hS, R, X
              approaches:=hE, paths:= OPE.Levy.tickets F R X ha U hT },h_extra0,hRR⟩
theorem pickWith {P_extra : RG.Levels G→Prop} (h_extra : Witness.Demandable P_extra) (h:G.Simple) {b:ℝ} (hb:0<b) : ∃ e:Exhibit G h b,P_extra e.C.path.levels:=by
    obtain ⟨V,h',H⟩:= pickJewel (Witness.nullR G) Witness.minimum h_extra h hb; exact ⟨V,h'⟩

theorem pick (G:Gauge) (h:G.Simple) {b:ℝ} (hb:0<b) : Nonempty (Exhibit G h b):= by obtain ⟨e,-⟩:= pickWith Witness.free_node h hb; exact ⟨e⟩
end Exhibit
end YM.RGComparison.Core16
