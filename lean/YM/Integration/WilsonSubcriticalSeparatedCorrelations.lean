import YM.Integration.WilsonCoefficientPreparation
import YM.Integration.WilsonSubcriticalPhysicalCorrelations
import YM.Integration.WilsonScalarFiledCorrelations

/-! Exact all-orders matching of every compact separated subcritical roster
on its original continuum hierarchy, in all states, at any common field
horizon. The two running changes act at the actual input dimensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalSeparatedCorrelations
open Function Filter Set Finset Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Pert Pert.Position Lattice Maxwell Maxwell.Free XSpace XSpace.Normalize
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale PhysicalNext.Repeat.Legato
open WilsonPositionSeparatedProfileOnePointMatched
open scoped Classical Topology BigOperators

variable {G : Gauge} {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {U : Table R.family.book}
  (F : Final R.family f U) (J : ℝ→tower U) (Z : WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  (simple : G.Simple) {P : Prescription (Press.portDeck G)} {dial : Bool}
  (named : Main.Match Z simple M P dial)

include R named in
private theorem constant_test {n : ℕ} (ν : ℝ) (h : ℕ) (φ : Test n) (c : Fin n→ℂ)
    (q : ℕ) (g : ℝ) :
    (∑ k∈range (q+1),(g:ℂ)^k * φ.applyTo (fun x=>
      if hx:x∈conf n then Facets.actMark (Measure.Z Z.scheme Z.criterion ν M h)
        (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M h)) n ⟨x,hx⟩ k
        (fun i=>c i • leaf G h) else 0))=φ.applyTo (fun _=>∏i,c i) := by
  have term (k : ℕ) :
      φ.applyTo (fun x=> if hx:x∈conf n then Facets.actMark (Measure.Z Z.scheme Z.criterion ν M h)
        (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M h)) n ⟨x,hx⟩ k
          (fun i=>c i • leaf G h) else 0) =
      if k=0 then φ.applyTo (fun _=>∏i,c i) else 0 := by
    trans φ.applyTo (fun _=>if k=0 then ∏i,c i else 0)
    · apply φ.apply_eq
      intro x hx
      simp only [dif_pos hx]
      exact WilsonScalarFiledCorrelations.coefficient R.family simple Z M named ν h ⟨x,hx⟩ c k
    · split_ifs
      · rfl
      · simp [Test.applyTo]
  simp [term,mul_ite]

include F J named in
theorem units (lead : Leading F J) {n : ℕ} (d : Fin n→ℕ) (h : ℕ) (room : ∀i,d i≤h)
    (a b : (i:Fin n)→ℝ→Change G (d i)) (c : Fin n→ℂ) (ν : ℝ) (φ : Test n) :
    ∀ᶠr in trail,∀(p:Viewers F)(q:ℕ)(g:ℝ),
      φ.applyTo (fun x=>U.classMoment (spectator F p) d (r•x)
        (fun i=>J r (d i) (adjusted R.family (d i) (b i r) (adjusted R.family (d i) (a i r)
          ((fields R.family.labels (d i)).symm (c i • leaf G (d i))))))) =
      ∑k∈range (q+1),(g:ℂ)^k * φ.applyTo (fun x=>if hx:x∈conf n then
        Facets.actMark (Measure.Z Z.scheme Z.criterion ν M h)
          (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M h)) n ⟨x,hx⟩ k
          (fun i=>up (room i) (c i • leaf G (d i))) else 0) := by
  have horizon (i : Fin n) : up (room i) (c i • leaf G (d i))=c i • leaf G h := by
    rw [map_smul]
    rfl
  filter_upwards [WilsonSubcriticalPhysicalCorrelations.observed F J lead d a b c φ] with r measured p q g
  simp only [horizon]
  exact (measured p).trans (constant_test (R:=R) Z M simple named ν h φ c q g).symm

include F J named in
theorem original (lead : Leading F J) {n : ℕ} (d : Fin n→ℕ) (low : ∀i,d i<4)
    (h : ℕ) (room : ∀i,d i≤h) (a b : (i:Fin n)→ℝ→Change G (d i))
    (v : (i:Fin n)→Sec G (d i)) (ν : ℝ) (φ : Test n) :
    ∀ᶠr in trail,∀(p:Viewers F)(q:ℕ)(g:ℝ),
      φ.applyTo (fun x=>U.classMoment (spectator F p) d (r•x)
        (fun i=>J r (d i) (adjusted R.family (d i) (b i r) (adjusted R.family (d i) (a i r)
          ((fields R.family.labels (d i)).symm (v i)))))) =
      ∑k∈range (q+1),(g:ℂ)^k * φ.applyTo (fun x=>if hx:x∈conf n then
        Facets.actMark (Measure.Z Z.scheme Z.criterion ν M h)
          (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M h)) n ⟨x,hx⟩ k
          (fun i=>up (room i) (v i)) else 0) := by
  choose c unit using fun i=>WilsonSubcriticalPhysicalCorrelations.scalar R.family simple (low i) (v i)
  rw [show v=(fun i=>c i • leaf G (d i)) from funext unit]
  exact units F J Z M simple named lead d h room a b c ν φ

end YM.Integration.WilsonSubcriticalSeparatedCorrelations
