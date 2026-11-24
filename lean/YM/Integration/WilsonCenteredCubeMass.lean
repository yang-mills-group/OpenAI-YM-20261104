import YM.Integration.WilsonCenteredCompactBooking
import YM.FrontierTrace.Primary.Junction

/-! The original rounded Wilson extraction for the whole compact source, with
the actual integrated child-cell masses at every cutoff and every real radius. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCubeMass
open Function Set Filter MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching
open WilsonCenteredCompactBooking WilsonCenteredPhysicalPanel
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n : ℕ} {f : Extraction.Order} {S : Table R.family.book}

private theorem restrict_test (t : Test n) (k : Points n → ℂ) :
    (∫x in tsupport (t : Points n → ℂ),t x*k x)=t.applyTo k :=by
  rw [← integral_indicator t.hasCompactSupport.measurableSet]
  unfold Test.applyTo
  congr 1
  funext x
  by_cases hx : x ∈ tsupport (t : Points n → ℂ)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    have h : t x=0 :=by
      by_contra neq
      exact hx (subset_closure neq)
    rw [h,zero_mul]

/-- The period condition precedes the UV limit. The outer limit uses the same
reader and the actual compact test without rounding the test values. -/
theorem original (F : Spec.Final R.family f S) (simple : G.Simple)
    (caps : Fin n → ℕ) (w : ∀j,R.family.label (caps j)) (φ : Test n) {r : ℝ} (hr : 0 < r) :
    ∃ pred : ℕ → Prop, f.limits pred
      (fun N p=>R.family.omega N p (cylinder R caps (N,p) w (mass R φ r (N,p))))
      (S.integralOn caps w (dilate hr φ)) :=by
  let t := dilate hr φ
  let K := tsupport (t : Points n → ℂ)
  let q : Fin n → R.family.book.Token := fun j=>⟨caps j,w j⟩
  obtain ⟨pred,actual⟩ := YM.FrontierTrace.Primary.Junction.junction_tail F
    (K:=K) (μ:=volume.restrict K) q id (t : Points n → ℂ) (R.again simple).1.control
    continuous_id t.hasCompactSupport (fun _ hx=>t.tsupport_subset hx)
    (ae_restrict_mem t.hasCompactSupport.measurableSet)
    (ae_restrict_of_ae (almostGeneric n))
    (t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport).restrict
  refine ⟨pred,?_⟩
  have pos (N p:ℕ) : (∫x in K,t x * (rounded R.family N p).read (id x) q) =
      R.family.omega N p (cylinder R caps (N,p) w (mass R φ r (N,p))) :=by
    rw [restrict_test]
    change (dilate hr φ).applyTo _ = _
    rw [zoom_integral,WilsonCenteredCompactBooking.exact R caps φ r (N,p) w]
    rfl
  have lim : (∫x in K,t x * S.read (id x) q) = S.integralOn caps w (dilate hr φ) :=by
    rw [restrict_test]
    rfl
  simp_rw [pos,lim] at actual
  exact actual

end YM.Integration.WilsonCenteredCubeMass
