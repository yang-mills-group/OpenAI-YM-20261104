import YM.AllOrder.Construction.Noel
import YM.PertExtension.UVBranch
import YM.TraceExtension.Followup2
import YM.OPE.Nesting.Endpoint

/-!
# Same-construction theorem for trace, OPE, and matching supplies

Includes the strengthened location supplies for PertExtension.Actual,
so we may use the leading scaling-frame convergence on THE table/Final,
at the same time as the trace and Nesting. No limit rate beyond the stated
supplies, conversion to all-order X space, or estimate for free comparison of
OPE coefficients is being assumed.

Lower-level `PhysicalNext.Repeat.Legato.merano_C` allows further increases in
before-L, delay and Wait, needed (as more is proved) to pay for all-order
matching. Retains the same field/curve/witness ties here as the trace producer
using squad_columns for the actual cylinders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder
open Function Filter Set MeasureTheory Analysis Extraction Table Climb Org Cells Ward
open PertExtension MergeProof.Acme Next.UVStress Trace OPE
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}

/-- Obtain Actual/F and Services for use in matching, at the output of one
construction also supporting the trace. Adapted from `stamped_temple`. -/
lemma joined (h : G.Simple) (b : ℝ) (hb : 0 < b) (f : Extraction.Order) :
    ∃ (C : Family G), C.Makes ∧ C.path.levels.clock.kernel.penalty = b ∧
      Extraction.Wcmain C ∧ (∀ d, Bid.pop (C.localSection d)) ∧
      ∃ (g : Extraction.Order) (S : Table C.book), Trace.Over.Gallery C (f.refine g) ∧
        OPE.Services C (f.refine g) S ∧ Nonempty (PertExtension.Actual C (f.refine g) S) := by
  obtain ⟨C,hB,hC,hM,hW,hSer,hPop,H,hQ,hF⟩ := PhysicalNext.Repeat.Legato.noel_TC h hb
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
  exact ⟨C,hM,hB,hW,hPop,g,S,hgal, ⟨hs,h,hSer,A,L,R,E,hA⟩,
    ⟨F,E,ht,hA.clean.ready,hA.clean.tilt,M,I,p,hI,hX,X,hY,hZ,hL,hstress,hd,hT⟩⟩

universe u
variable (h : G.Simple) {C : Family G} {g : Extraction.Order} {S : Table C.book}

/-- Monotone under adding finite demands to the calendars in merano_C and the
recoveries above in the following sense: the proof can always build the
supplies together paying the `_TC`/`_C` schedule. *Not* asserting a
transport law to any other C. -/
structure SupportsMatching (F : Spec.Final C g S) : Prop where
  pop (d : ℕ) : Bid.pop (C.localSection d)
  services : OPE.Services C g S
  every : ∃ L : EveryPhase.Almanac F, EveryPhase.Completed F L
  result : Trace.Target.Result.{u} F h
  ope : ∃ R : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin,
    OPE.Orbits.Foundation F R ∧ OPE.Nesting.Uniform F R

/-- Uses Sect.Energy, all comparisons, OPE and phases of `A.F`.
`A` is the PertExtension witness carrying all-horizon weak unselected
comparison scales and fee-free leading stress in *that* scaling frame.
Nothing asserting positivity/uniformity beyond their hypotheses. -/
theorem matching_data (b : ℝ) (hb : 0 < b) (f : Extraction.Order) :
    ∃ (C : Family G), C.path.levels.clock.kernel.penalty = b ∧ Extraction.Wcmain C ∧
    ∃ (q : Extraction.Order) (S : Table C.book) (A : PertExtension.Actual C (f.refine q) S),
      SupportsMatching.{u} h A.F := by
  obtain ⟨C,-,hB,hW,hP,q,S,hG,hServ,⟨A⟩⟩ := joined h b hb f
  refine ⟨C,hB,hW,q,S,A,hP,hServ,EveryPhase.all_characters A.F,
    Trace.Target.assembled A.F h (arenaT A.F h (crest_ready _ h hG)),?_⟩
  obtain ⟨p,hp⟩ := OPE.Prescription.chosen A.F.room.kernel.laws.toSymmetric
    A.F.phase.transport.injection
  let R : OPE.Orbits.Reader A.F.sector.derivatives A.F.sector.turns A.F.room.kernel.spin :=
    ⟨p,hp,A.F.room.kernel,A.F.phase.transport.injection,A.F.phase.transport.rights,
     A.F.phase.transport.spots⟩
  exact ⟨R, OPE.Orbits.produce A.F R hServ,OPE.Nesting.uniform A.F R hServ⟩

end YM.AllOrder
