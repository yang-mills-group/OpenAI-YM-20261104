import YM.Integration.WilsonMatrixOriginalDeckSignedHorizon
import YM.Integration.WilsonReportingMeasuredTender
import YM.Integration.WilsonReportingMeasuredAdmission

/-! Original all-height Wilson deposits for the measured frame at two independently chosen radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckFiled
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Menus MS.Local.Physical MS.Land MS.Theater
open Extraction Extraction.Order Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Table Ward PhysMS RG17 RG12 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato Pier.Lair SharpGram SharpGram.Lenses
open WilsonMatrixOriginalDeckRegulated WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckColumns
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- Full physical two-field product with both old labels followed to this actual cutoff, at the two separate dates. -/
def operand (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) (w v:R.family.label h) (z:ℕ×ℕ) : ℂ :=
  reading (R:=R) h g hr (fun k=>![atRef L h r k w,atRef L h s k v]) z

/-- A filed pair with actual reported labels measures the same complete mixed matrix on the original Wilson law. -/
theorem issued (g:Test 2) {r s:ℝ} (hr:0<r) (first:R.family.ref h≤L.level r) (second:R.family.ref h≤L.level s)
    (a b:Glyph B h) (w v:R.family.label h)
    (row:master L h r w=J r h (WilsonMatrixOriginalDeckColumns.basis R.family B h a)) (column:master L h s v=J s h (WilsonMatrixOriginalDeckColumns.basis R.family B h b))
    (u:Filter (ℕ×ℕ)) [u.NeBot] (cut:u≤L.lens) :
    Tendsto (operand R F L h g hr s w v) u (𝓝 (mixed B J h g r s a b)) := by
  apply WilsonMatrixOriginalDeckRegulated.measured B F J h g hr s a b u (cut.trans L.certified)
    (fun k=>![atRef L h r k w,atRef L h s k v]) ![locatedRef L h r w,locatedRef L h s v]
  · intro i
    fin_cases i
    · exact RG17.tendsRef L cut (v:=fun _=>w) tendsto_const_nhds first
    · exact RG17.tendsRef L cut (v:=fun _=>v) tendsto_const_nhds second
  · intro i
    fin_cases i
    · exact (RG17.payRef L w).trans row
    · exact (RG17.payRef L v).trans column

/-- One exponent on this original selection and one entire system of pre-cutoff depositors. The
coarse clock and all true incoming labels are selected before tests, later cutoff and period. -/
theorem purchased (leading:PhysMS.Leading F J) {K:(Bel R.family.book).Hierarchy}
    (alignment:∀d:ℕ,∀ᶠr in Trace.Pilot.trail,AlignO F.sector F.room.kernel.spin K d (J r d))
    {u₀:Filter (ℕ×ℕ)} (mantle:Mantle F u₀) (services:Services R.family f S) (pegs:Pegs mantle L)
    (near:∀ᶠr in Trace.Pilot.trail,R.family.S.a (L.level r)≤r ∧ r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2) :
    ∃e:ℕ,∃W:Set ℝ,W∈Trace.Pilot.trail ∧ ∃w:(r:W)→Glyph B h→R.family.label h,
      (∀(r:W),0<r.val ∧ R.family.ref h≤L.level r.val ∧ ∀a,
        mass R.family h (L.shift h r.val (w r a)) ≤ R.family.path.levels.clock.hatBeta (L.level r.val)^e*‖WilsonMatrixOriginalDeckColumns.basis R.family B h a‖ ∧
        master L h r.val (w r a)=J r.val h (WilsonMatrixOriginalDeckColumns.basis R.family B h a)) ∧
      ∀ (g:Test 2) (r s:W) (hr:0<r.val) (a b:Glyph B h) (u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens →
        Tendsto (operand R F L h g hr s.val (w r a) (w s b)) u (𝓝 (mixed B J h g r.val s.val a b)) := by
  obtain ⟨e,rows⟩ := WilsonReportingMeasuredTender.entry mantle services
    (WilsonReportingMeasuredAdmission.present F J leading alignment) pegs near h
  have opened : ∀ᶠr in Trace.Pilot.trail,R.family.ref h≤L.level r := pegs.level.growing.eventually_ge_atTop _
  obtain ⟨W,hW,times⟩ := Filter.Eventually.exists_mem (positiveLength.and (opened.and rows))
  choose w paid field using fun (r:W) (a:Glyph B h)=>(times r.val r.property).2.2 (WilsonMatrixOriginalDeckColumns.basis R.family B h a)
  refine ⟨e,W,hW,w,fun r=>⟨(times r r.property).1,(times r r.property).2.1,fun a=>⟨paid r a,field r a⟩⟩,?_⟩
  intro g r s hr a b u _ cut
  exact issued R B F L J h g hr (times r r.property).2.1 (times s s.property).2.1 a b (w r a) (w s b)
    (field r a) (field s b) u cut

end YM.Integration.WilsonMatrixOriginalDeckFiled
