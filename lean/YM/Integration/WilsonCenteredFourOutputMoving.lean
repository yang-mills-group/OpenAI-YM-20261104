import YM.Integration.WilsonPublicOutputRows
import YM.Integration.WilsonCenteredFourOutputOperator

/-! A single positive binary coefficient on the original finite moving
detector, including the complete printed lower basis in its Gram expense. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourOutputMoving
open Filter Set Table Spec OPE OPE.Orbits OPE.Log PhysMS Trace Trace.Pilot Trace.Terrace Climb
open FVA2 FVA2.Register FVA2.ColorCode FVA2.Scale Pert Pert.Position MS MS.Local.Physical XSpace XSpace.Normalize
open MS.Menus MS.Land MS.Theater RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonCenteredFourOutputSensor WilsonPublicOutputRows GapsContact GapsContact.Seams
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (J:ℝ→tower S) (Z:WilsonPrescription G)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "d₄" => (fun _:Fin 2=>4)
local notation "Print" => Press.portDeck G
local notation "formal" => WilsonMacroscopicRichMSCoefficient.field
local notation "fee" => WilsonMacroscopicRichMSCoefficient.coefficient

theorem original (simple:G.Simple) (fac:Facilities R.family f S) {l:Ultrafilter (ℕ×ℕ)} (lo:(l:Filter _)≤f.fuse)
    (ticket:MatrixTicket (C:=R.family) S F.sector.derivatives (l:Filter _)) {arch:Arch R.family}
    {Y:(Bel R.family.book).Hierarchy} (bliss:Bliss F l arch Y) (V:Store G) (lead:Leading F J)
    (owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d) (c:Q.channels 4):
    LogTrace F Q.port ∧
    ∃B:Profiles R 4,∃w:B.probes.index→Atom (R:=R) 4,
    ∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid 4 (w j),
    ∃(j:ℕ)(L:ℝ),0≤L ∧ ∀g:ℝ→ℝ,Coupling G g→∀P E A:ℕ,P+E≤A →
    ∀ᶠr in trail,let t:=r/((g r)^A)^2;∃tp:0<t,∀(M:MS_Data G (Position.OpenAxis.Plot Print))
      (v:Fin 2→(Bel R.family.book).Field 4) (x:Points 2) (μ:ℝ) (q:ℕ)
      (joint:B.probes.index→ℂ) (gram:Glyph Print 4→B.probes.index→ℂ) (C D:ℝ),0≤C →
      let observed:=sample F J Z B w issued tp r x (fun i=>⟨4,v i⟩)
      let measured:=WilsonPublicOutputRows.packet F J Q 4 d₄ v r x
      let a:=fun b:Glyph Print 4=>fee R M d₄ v μ x (g r) q b
      let bills:=‖observed-joint‖+‖joint-∑b,a b • gram b‖+
        ∑b,‖a b‖*‖gram b-row F J Z B t (J r 4 (axis (R:=R) 4 b))‖
      ‖row F J Z B t measured-observed‖≤C*(((g r)^A)^2)^5/(g r)^E →
      bills≤D*(g r)^(P+A*9) →
      ‖Q.coef 4 c (fun i=>r • x i) (Frame.born J r (d:=d₄) v) 0-
        grade F Q c (J r 4 (formal R M 4 d₄ v μ x (g r) q))‖ ≤
      L*dock r^j*r^4*(C+D)*(g r)^P:=by
  obtain ⟨logged,B,w,issued,K,kp,read⟩:=WilsonPublicOutputRows.original F J Z lead owed simple Q fac lo ticket 4
  obtain ⟨j,H,hp,positive⟩:=WilsonCenteredFourOutputOperator.paid F Q J (simple:=simple) bliss ticket V lead c
  refine ⟨logged,B,w,issued,j,H*K,mul_nonneg hp kp,fun g hg P E A order =>?_⟩
  have small:∀ᶠr in trail,r≤1:=(ge_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [read g hg P E A order,positive,small,self_mem_nhdsWithin] with r rows direct small pos t
  obtain ⟨tp,priced⟩:=rows
  refine ⟨tp,?_⟩
  intro M v x μ q joint gram C D cp observed measured a bills sharp tested
  let y:=formal R M 4 d₄ v μ x (g r) q
  have vector:=priced M 2 d₄ v x μ (g r) q joint gram C D cp sharp tested
  have dk:0≤dock r:=zero_le_one.trans (dock_valid r ⟨pos,small⟩)
  rw [←WilsonCenteredFourOutputSensor.packet F Q c]
  exact (direct measured y).trans ((mul_le_mul_of_nonneg_left vector (by positivity)).trans_eq (by ring))

end YM.Integration.WilsonCenteredFourOutputMoving
