import YM.Integration.WilsonSeparatedTubePhysicalPlane
import YM.Integration.WilsonSeparatedTubeCauchy

/-! Genuine directional derivatives on the original scaled Euclidean hierarchy, for
every independently paid finite array of local fields, in any of its orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalOrderedJets
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open WilsonSeparatedTubeCoordinates
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {l : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}

theorem purchased (hG : G.Simple) (bliss : Bliss F l Z H) {n : ℕ} (d : Fin n → ℕ)
    {B : ℝ} (hB : 0 ≤ B) (P : Set (Points n)) (hp : IsCompact P)
    (ordered : ∀ x∈P, (fun i=>YM.time (x i))∈east n) :
    ∃ ρ : ℝ, 0<ρ ∧ ∃ δ∈Ioc (0:ℝ) 1, ∃ A : ℝ, 0≤A ∧ ∃ p : ℕ,
    ∀ᶠ r in trail, ∀ (σ : Equiv.Perm (Fin n)) (v : ∀ i,S.Field (d (σ i))),
      (∀ i, Ascent.cost F (d (σ i)) r (v i) ≤ B) → ∀ x∈P, ∀ u : Points n, ‖u‖≤1 → ∀ j : ℕ,
      ‖iteratedDeriv j (fun t : ℝ=> S.classMoment S (fun i=>d (σ i)) (r • (x+t • u)) v) 0‖ ≤
      j.factorial * (A*(LogV r/δ)^p) / ρ^j := by
  obtain ⟨L⟩ := almanac F
  obtain ⟨Y,-,seen⟩ := (Survey.fits L (none : Survey F)).reveals
  obtain ⟨D,X,-⟩ := (seen F.action.J F.realization.qt.induced).1.visible
  let e : Points n →L[ℝ] Full n := embedding.comp coordinates
  have inside : e '' P ⊆ tube n := by
    rintro _ ⟨x,hx,rfl⟩
    exact plane_inside (coordinates x).1 (ordered x hx)
  obtain ⟨ρ,hρ,δ,hδ,A,hA,p,paid⟩ := WilsonSeparatedTubeCauchy.complex F hG bliss L d hB _
    (hp.image e.continuous) inside
  refine ⟨ρ,hρ,δ,hδ,A,hA,p,?_⟩
  filter_upwards [paid,self_mem_nhdsWithin (a:=0)] with r cost hr
  intro σ v bound x hx u hu j
  let g (z : ℂ) := weather X (WilsonSeparatedTubeEnvelope.tag v) r (e x+z • e u)
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, (coordinates (x+t • u)).2∈east n := by
    have c : Continuous (fun t : ℝ => (coordinates (x+t • u)).2) := by fun_prop
    have z : (coordinates (x+ (0:ℝ) • u)).2∈east n := by
      rw [zero_smul,add_zero]
      change (fun i=>YM.time (x i))∈east n
      exact ordered x hx
    exact c.continuousAt.eventually ((open_east n).mem_nhds z)
  have agree : (fun t : ℝ=>S.classMoment S (fun i=>d (σ i)) (r • (x+t • u)) v) =ᶠ[𝓝 0] fun t : ℝ =>g t := by
    filter_upwards [hpos] with t h
    have real_read := (WilsonSeparatedTubePhysicalPlane.read F L D X v hr
      (coordinates (x+t • u)).1 (coordinates (x+t • u)).2 h).symm
    rw [rebuild] at real_read
    calc _ = weather X (WilsonSeparatedTubeEnvelope.tag v) r (e (x+t • u)) := real_read
         _ = _ := by simp only [g,map_add,map_smul,Complex.coe_smul]
  have analytic := (hollow X (observe L none X).2 (WilsonSeparatedTubeEnvelope.tag v) r hr) (e x)
    (inside (mem_image_of_mem e hx))
  have hol : AnalyticAt ℂ g 0 := by
    have at_center : AnalyticAt ℂ (weather X (WilsonSeparatedTubeEnvelope.tag v) r) (e x+(0:ℂ) • e u) := by
      simpa only [zero_smul,add_zero] using analytic
    have ray : AnalyticAt ℂ (fun z : ℂ=>e x+z • e u) 0 := by fun_prop
    exact AnalyticAt.comp (f:=fun z : ℂ=>e x+z • e u) (x:=0) at_center ray
  rw [agree.iteratedDeriv_eq j,WilsonSeparatedTubeCauchy.real_jet hol]
  exact cost σ v bound none D X (e x) (mem_image_of_mem e hx) (e u) ((isometry u).trans_le hu) j

end YM.Integration.WilsonSeparatedPhysicalOrderedJets
