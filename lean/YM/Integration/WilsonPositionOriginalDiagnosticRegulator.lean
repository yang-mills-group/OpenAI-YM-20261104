import YM.Integration.WilsonPositionOriginalDiagnosticHearing
import YM.Integration.WilsonPositionOriginalDiagnosticPurse
import YM.Integration.WilsonPositionCapTransport

/-! The complete finite-cutoff field-normalization fee on the actual marked
Wilson integrals. Its limit is the purse for the same physical correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRegulator
open Function Filter Set Finset Metric MeasureTheory Extraction Table Spec OPE Climb PhysMS Maxwell
open Trace.Pilot XSpace XSpace.Normalize XSpace.Normalize.Fray FVA2 FVA2.Arrival MS MS.Land
open MS.Local.Physical MS.Menus MS.Theater Lattice RG RG17 PhysicalNext.Repeat.Legato
open WilsonPositionThermometerCapStation WilsonPositionOriginalDiagnosticRead
open WilsonPositionOriginalDiagnosticGrades WilsonPositionOriginalDiagnosticPurse
open WilsonPositionPrescribedFormalTest WilsonPositionThermometerOrientedStation
open RG12
open scoped Topology BigOperators Classical
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {h d:ℕ} (A:ℝ→Group R.family h) (fit:d≤h) (B:Deck G) (V:Store G)

def word (w:Window G d) (a:Fin w.n→Glyph B d) (r:ℝ) (z:UVIndex) : ℂ :=
  w.t.applyTo (WilsonPositionOriginalDiagnosticCells.cut (R:=R) (fun i=>(a i).size)
    (fun ζ i=>upper B (A r) fit (a i) ζ) r z)

def cost (w:Window G d) (Q:Prediction G d) (r:ℝ) (z:UVIndex) : ℝ :=
  ∑ a:Fin w.n→Glyph B d, ‖weight B w a‖ * ‖word A fit B w a r z - reading B Q w a‖

def price (Q:Prediction G d) (r:ℝ) (z:UVIndex) : ℝ :=
  ∑ i:Fin (V.survey d).n, ∑ k:Fin ((V.survey d).scope i).n→Pin G d,
    cost A fit B (fixed V i k) Q r z

variable (F:Final R.family f S) (J:ℝ→tower S) (lead:PhysMS.Leading F J)
variable {Y:Ultrafilter UVIndex} (hl:(Y:Filter UVIndex)≤f.fuse) (simple:G.Simple)
    {H:(Bel R.family.book).Hierarchy} (book:WilsonPositionCapTransport.Book (f:=f) (l:=Y) (H:=H) A J)

include lead hl simple book in
theorem received : ∀ᶠ r in trail, ∀ Q:Prediction G d,
    Tendsto (price A fit B V Q r) (Y:Filter UVIndex)
      (𝓝 (invoice B V (WilsonPositionPrescribedScreen.hierarchy F J d r) Q)) := by
  have hh := WilsonPositionOriginalDiagnosticHearing.original F J hl A fit B simple H lead
    (fun i:WilsonPositionCapTransport.Address R.family h=>i.1) WilsonPositionCapTransport.entry 0 (book 0)
  filter_upwards [hh] with r filed Q
  have take (w:Window G d) :
      Tendsto (cost A fit B w Q r) (Y:Filter UVIndex) (𝓝 (bill B w (WilsonPositionPrescribedScreen.hierarchy F J d r) Q)) := by
    exact tendsto_finsetSum _ fun a _=>tendsto_const_nhds.mul ((filed w a).sub tendsto_const_nhds).norm
  exact tendsto_finsetSum _ fun i _=>tendsto_finsetSum _ fun k _=>take (fixed V i k)

variable (ν:ℝ) (T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (q:ℕ)

include lead hl simple book in
theorem actual {t:ℝ→ℝ} (small:Tendsto t trail (𝓝 0)) :
    ∃ L b:ℝ,0≤L ∧ 0≤b ∧ ∀ᶠ r in trail, ∀ ε:ℝ, 0<ε → ∀ᶠ z in (Y:Filter UVIndex),
      ‖guide G d (WilsonPositionPrescribedScreen.correction F J V d r) -
        WilsonPositionPrescribedRootPrice.native V ν T d q (t r)‖ ≤
      L*price A fit B V (raw ν T d q (t r)) r z + b*|t r|^(q+1) + ε := by
  obtain ⟨L,b,hL,hb,credit⟩:=WilsonPositionOriginalDiagnosticPurse.original B V ν T q F J lead small
  refine ⟨L,b,hL,hb,?_⟩
  filter_upwards [credit,received A fit B V F J lead hl simple book] with r cap available ε he
  let Q:=raw ν T d q (t r)
  let P:=WilsonPositionPrescribedScreen.hierarchy F J d r
  have limit:Tendsto (fun z=>L*price A fit B V Q r z) (Y:Filter UVIndex) (𝓝 (L*invoice B V P Q)) :=
    tendsto_const_nhds.mul (available Q)
  filter_upwards [limit.eventually (lt_mem_nhds (show L*invoice B V P Q-ε<L*invoice B V P Q by linarith))] with z near
  exact cap.trans (by dsimp only [P,Q] at near; linarith)

end YM.Integration.WilsonPositionOriginalDiagnosticRegulator
