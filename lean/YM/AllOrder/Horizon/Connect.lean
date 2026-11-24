import YM.AllOrder.Horizon.Garland
import YM.AllOrder.Leading.Calibration
/-! # Same Compatible lifts & first matching from CP1 -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder
open Function Filter Set MeasureTheory Analysis Extraction Table Climb Org Cells Ward
open PertExtension MergeProof.Acme Next.UVStress Trace OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}

/-- Obtain Actual/F and Services for use in matching, at the output of one
construction also supporting the trace. Adapted from `stamped_temple`. -/
lemma pledged_family (h : G.Simple) (b : ℝ) (hb : 0 < b) (f : Extraction.Order) :
    ∃ (C : Family G), C.Makes ∧ PhysicalNext.Repeat.Legato.CentralS C ∧ C.path.levels.clock.kernel.penalty = b ∧
      Extraction.Wcmain C ∧ (∀ d, Bid.pop (C.localSection d)) ∧
      ∃ (g : Extraction.Order) (S : Table C.book), Trace.Over.Gallery C (f.refine g) ∧
        OPE.Services C (f.refine g) S ∧ Nonempty (PertExtension.Actual C (f.refine g) S) := by
  obtain ⟨C,hXc,hB,hC,hM,hW,hSer,hPop,H,hQ,hF⟩ := PhysicalNext.Repeat.Legato.noel_H h hb
  obtain ⟨g,A,L,R,S,E,hA,s,hN⟩ := hF f
  obtain ⟨hs,hG,hgal⟩ := hQ (f.refine g) s.copies
  obtain ⟨T₀,_,_⟩ := Maxwell.Free.maxwell_supplies C h 1 one_ne_zero
  obtain ⟨M,hstress,_,_,_,_,_,hd⟩ := YM.UVNext.FreeStress.fire h T₀ 1 one_ne_zero
  have hh := M.hT.smooth
  have hS := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin
    (fun N D R hr => hG N D R (zero_lt_one.trans_le hr) hh _)
  obtain ⟨hf,I,X,hI,hX,hY,hZ,hL,hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel
    s.copies hA.clean.ready hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges
    M.lit.pales M.lit.hers hd hS H
  have p : UV C (f.refine g) S E M I := ⟨s,hf,hp,ha,hs⟩
  obtain ⟨F,-,ht,hT⟩ := relevant p X hA.clean.ready hA.clean.tilt hY hZ hL hd hX hI hC
  exact ⟨C,hM,hXc,hB,hW,hPop,g,S,hgal, ⟨hs,h,hSer,A,L,R,E,hA⟩,
    ⟨F,E,ht,hA.clean.ready,hA.clean.tilt,M,I,p,hI,hX,X,hY,hZ,hL,hstress,hd,hT⟩⟩

universe u
variable (h : G.Simple) {C : Family G} {g : Extraction.Order} {S : Table C.book}

/-- Uses Sect.Energy, all comparisons, OPE and phases of `A.F`.
`A` is the PertExtension witness carrying all-horizon weak unselected
comparison scales and fee-free leading stress in *that* scaling frame.
Nothing asserting positivity/uniformity beyond their hypotheses. -/
theorem match_high (b : ℝ) (hb : 0 < b) (f : Extraction.Order) :
    ∃ (C : Family G), PhysicalNext.Repeat.Legato.CentralS C ∧ C.path.levels.clock.kernel.penalty = b ∧ Extraction.Wcmain C ∧
    ∃ (q : Extraction.Order) (S : Table C.book) (A : PertExtension.Actual C (f.refine q) S),
      SupportsMatching.{u} h A.F := by
  obtain ⟨C,-,hX,hB,hW,hP,q,S,hG,hServ,⟨A⟩⟩ := pledged_family h b hb f
  refine ⟨C,hX,hB,hW,q,S,A,hP,hServ,EveryPhase.all_characters A.F,
    Trace.Target.assembled A.F h (arenaT A.F h (crest_ready _ h hG)),?_⟩
  obtain ⟨p,hp⟩ := OPE.Prescription.chosen A.F.room.kernel.laws.toSymmetric
    A.F.phase.transport.injection
  let R : OPE.Orbits.Reader A.F.sector.derivatives A.F.sector.turns A.F.room.kernel.spin :=
    ⟨p,hp,A.F.room.kernel,A.F.phase.transport.injection,A.F.phase.transport.rights,
     A.F.phase.transport.spots⟩
  exact ⟨R, OPE.Orbits.produce A.F R hServ,OPE.Nesting.uniform A.F R hServ⟩

end YM.AllOrder

namespace YM.AllOrder
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Trace.Terrace Analysis
open OPE OPE.Orbits MeasureTheory PositionX PositionX.Bend Leading
open scoped BigOperators Topology Classical ContDiff
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

/-- Wilson schedule/final carrying the exact frame, leading matching and
 OPE/nonzero-trace. Entry on the same construction. `S` seed and Final in A,
not claiming other components about separately packaged FullVolume results.
`aligned` charges in the still-leading coupling convention `glo`. -/
theorem priced_first_match (h : G.Simple) (b : ℝ) (hb : 0<b) (p : Extraction.Order) :
    ∃ (C : Family G), PhysicalNext.Repeat.Legato.CentralS C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧
    ∃ (q : Extraction.Order) (S : Table C.book) (A : PertExtension.Actual C (p.refine q) S),
      SupportsMatching.{u} h A.F ∧
       (∃ (H : (Bel C.book).Hierarchy) (Z : Arch C) (l : Ultrafilter (ℕ × ℕ))
           (P P' : ℝ → Spin.change S 4) (χ : E4 → ℝ) (κ d e : ℝ → ℝ) (K : PositionX.Bare.Shop C.labels)
           (c : ℝ) (T : PositionX.Bend.Booth c C.labels) (U : ℝ → FamilyFrame S)
           (R : Reader A.F.sector.derivatives A.F.sector.turns A.F.room.kernel.spin),
         Trace.Target.XScheme A.F h H l P P' χ ∧
         Trace.Target.FieldComparison A.F H Z P P' κ d e ∧ Bliss A.F l Z H ∧
         FirstMatch A.F h R (Sundial.glo P') U K c T) := by
    obtain ⟨C,hC,hB,hW,q,S,A,hF⟩ := match_high.{u} h b hb p
    let F:= A.F
    have hp := hF.services
    obtain ⟨R,hP⟩:= hF.ope
    obtain ⟨H,Z,l,hV,⟨χ,P,P',hS⟩,hQ⟩ := hF.result.stress
    obtain ⟨κ,d,e,he⟩ := hQ χ P P' hS
    obtain ⟨U,hU⟩ := aligned_exists h hV he.coupling
    let K : PositionX.Bare.Shop C.labels := ⟨C.params, C.localSection,A.F.room.cutoff.sections,hF.pop⟩
    obtain ⟨c,T,hx⟩ := can_booth K h
    obtain ⟨ht,hL⟩:= solves_position_in_frame hU K h
    refine ⟨C,hC,hB,hW,q,S,A,hF,H,Z,l,P,P',χ,κ,d,e,K,c,T,_,R,hS,he,hV,ht,hL,hp,rfl,rfl,
       fun q hq=>PositionX.lit h T q hq K (hx q hq).2, fun q hq _ _=> Bend.θ_up K q h T hq,hP,
       fun q hq d n v p => leading_edge K q h T hq (⟨n,v,p⟩:Pert.Position.Section C.labels d),
       ?_, fun _ _ _ v _ _ hη ε he=> Leading.plate R v ht hp h hη he⟩
    intro d n v p s
    exact test_tend R (d:=fun _=>d) v ht hp h p s
end YM.AllOrder
