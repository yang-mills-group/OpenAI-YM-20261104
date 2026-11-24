import YM.Integration.WilsonAllDateHarvestCenteredLedger
import YM.Integration.WilsonReportHarvestLedgerFlat
import YM.Integration.WilsonReportHarvestResidentRootFee
import YM.Integration.WilsonSeparatedOriginalJointLog

/-! The actual signed three-point comparison to the separately advanced
original deletion trajectory on its own healthy reporting field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalCloseLedger
open Function Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extra.Histories Push Local
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Records RG05Readout.Address
open Extra.Trajectories PhysicalNext.Repeat WilsonAllDateHarvestStability WilsonSeparatedOriginalResidentReadout
open WilsonSeparatedOriginalMarkedCubic
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{J:Census V}
variable {P:Rep G n}{rows:V→Three G n}{L Y:Config G n→Poly J}{o:V→Site n}{w:V→ℝ}{α δ:ℝ}

private lemma logged (B:Ledger P rows L o w α)(W:Config G n)(healthy:flags P.p.threshold W=∅):
    connected ((P.eval W:ℂ)⁻¹ • L W)=Mach J (fun i=>(rows i).2.1 W)+∑ X,B.H X W:=by
  have actual:=(WilsonReportHarvestLedgerFlat.returned P rows (fun _=>0) B.legal W healthy).2
  exact (congrArg (fun A:Config G n→Poly J=>connected ((P.eval W:ℂ)⁻¹ • A W)) B.paid).trans (by
    simpa only [add_zero] using actual)

/-- One anchored, signed rank of the genuine regular difference, with the
original phase, both independently evolved sheets and the same old vacuum. -/
theorem signed (B:Ledger P rows L o w α)(Z:Ledger P rows Y o w α)
    (payment:Towed (fun _:V=>(1:ℝ)) id (fun X U=>Z.H X U-B.H X U) P.p.B α δ)(expo:0 ≤ α)
    (W:Config G n)(healthy:flags P.p.threshold W=∅)(s:J.Mode)(i:V)(uses:i∈s.val):
    let actual:=(connected ((P.eval W:ℂ)⁻¹ • Y W)).part s
    let forecast:=(connected ((P.eval W:ℂ)⁻¹ • L W)).part s
    actual-forecast=(∑X:Support n,(Z.H X W-B.H X W).part s) ∧ ‖actual-forecast‖ ≤ δ:=by
  intro actual forecast
  have charged:=WilsonReportHarvestResidentRootFee.rooted payment expo s (o i) W (by
    intro X active;by_contra outside
    have absent:¬ (s.val:Set V)⊆{v|o v∈X}:=fun covered=>outside (covered uses)
    apply active
    change (Z.H X W).part s-(B.H X W).part s=0
    rw [(Z.legal.exp X).1.toBorne.scope W s absent,(B.legal.exp X).1.toBorne.scope W s absent,sub_self])
  have closed:actual-forecast=∑X:Support n,(Z.H X W-B.H X W).part s:=by
    change (connected _).part s-(connected _).part s=_
    rw [logged Z W healthy,logged B W healthy,Poly.part_plus,Poly.part_plus,Poly.part_sum,Poly.part_sum]
    change _=∑X:Support n,((Z.H X W).part s-(B.H X W).part s)
    rw [Finset.sum_sub_distrib];ring
  exact ⟨closed,closed ▸ charged.2⟩

/-- The parent capture's three genuinely observed Gibbs fields and its
beforehand chosen original lower replay. Close b_T needs no separation. -/
theorem measured (C:Family G)(made:C.Makes){N per j:ℕ}(jn:j ≤ N)(f:V→Goods G (C.side N per))
    (cf:∀v,Continuous (f v))(z:Fin 3 → V)(different:Injective z)(all:Finset.univ.image z∈J.choices)
    {rows:V → Three G (C.side j per)}{L:Config G (C.side j per) → Poly J}{o:V → Site (C.side j per)}
    {w:V → ℝ}(B:Ledger (C.path.rep N per j) rows L o w α)
    (Z:Ledger (C.path.rep N per j) rows (gust C.path N per N (birth J (C.path.rep N per N) f) j jn) o w α)
    (payment:Towed (fun _:V=>(1:ℝ)) id (fun X U=>Z.H X U-B.H X U) (C.path.rep N per j).p.B α δ)(expo:0 ≤ α)
    (W:Config G (C.side j per))(healthy:flags (C.path.rep N per j).p.threshold W=∅):
    ‖cubic (WilsonSeparatedOriginalMarkedCubic.moment C z f jn W)-
      (connected (((C.path.rep N per j).eval W:ℂ)⁻¹ • L W)).part (modes z all univ)‖ ≤ δ:=by
  have billed:Integrable (birth J (C.path.rep N per N) f) (prior G _):=
    (hatCont C N per f cf (show Continuous (C.path.rep N per N).eval by rw [(made.wilson.starts ..).2];exact bare_cont _) J).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have same(x:Poly J):narrow (le_refl J.choices) x=x:=by ext t;rw [narrow_right];rfl
  have actual:=WilsonSeparatedOriginalJointLog.measured C z f made different all (le_refl J.choices) billed jn W
  simp only [same] at actual
  rw [actual]
  exact (signed B Z payment expo W healthy (modes z all univ) (z 0) (Finset.mem_image_of_mem _ (mem_univ _))).2

end YM.Integration.WilsonSeparatedOriginalCloseLedger
