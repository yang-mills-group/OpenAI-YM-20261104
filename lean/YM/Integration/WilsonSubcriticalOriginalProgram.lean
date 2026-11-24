import YM.Integration.WilsonSubcriticalSeparatedCorrelations

/-! Select the actual independent prescription once on its requested
spacing and volume schedule before every subcritical correlation test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalOriginalProgram
open Function Filter Set Finset Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Pert Pert.Position Lattice Maxwell Maxwell.Free XSpace XSpace.Normalize
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale
open WilsonPositionSeparatedProfileOnePointMatched
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {U : Table R.family.book}
  (F : Final R.family f U) (J : ℝ→tower U)
  (Z : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))

def Compared : Prop :=
  ∀ (n : ℕ) (d : Fin n→ℕ), (∀i,d i<4) → ∀ (h : ℕ) (room : ∀i,d i≤h)
    (a b : (i:Fin n)→ℝ→Change G (d i)) (v : (i:Fin n)→Sec G (d i)) (ν : ℝ) (φ : Test n),
    ∀ᶠr in trail,∀(p:Viewers F)(q:ℕ)(g:ℝ),
      φ.applyTo (fun x=>U.classMoment (spectator F p) d (r•x)
        (fun i=>J r (d i) (adjusted R.family (d i) (b i r) (adjusted R.family (d i) (a i r)
          ((fields R.family.labels (d i)).symm (v i)))))) =
      ∑k∈range (q+1),(g:ℂ)^k * φ.applyTo (fun x=>if hx:x∈conf n then
        Facets.actMark (Measure.Z Z.scheme Z.criterion ν M h)
          (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M h)) n ⟨x,hx⟩ k
          (fun i=>up (room i) (v i)) else 0)

theorem genuine (simple : G.Simple) (lead : Leading F J) (dial : Bool) :
    ∃ P : Prescription (Press.portDeck G), Main.Match Z simple M P dial ∧ Compared F J Z M := by
  obtain ⟨P,named⟩:=Main.wilson_to_MS Z simple M dial
  exact ⟨P,named,fun _ d low h room a b v ν φ=>
    WilsonSubcriticalSeparatedCorrelations.original F J Z M simple named lead d low h room a b v ν φ⟩

theorem original (simple : G.Simple) (lead : Leading F J) (L : XSpace.Run) (dial : Bool) :
    ∃ (Z : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (P : Prescription (Press.portDeck G)), Z.run=L ∧ Main.Match Z simple M P dial ∧
        Compared F J Z M := by
  obtain ⟨Z,M,P,run,named⟩:=Main.solution G simple L dial
  exact ⟨Z,M,P,run,named,fun _ d low h room a b v ν φ=>
    WilsonSubcriticalSeparatedCorrelations.original F J Z M simple named lead d low h room a b v ν φ⟩

end YM.Integration.WilsonSubcriticalOriginalProgram
