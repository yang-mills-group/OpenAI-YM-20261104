import YM.Integration.WilsonPositionSeparatedProfileReportingVariation
import YM.Integration.WilsonReportingRegisteredWindows

/-! Local gauge-chart exceptions in the complete registered spatial test,
including their propagation to every earlier translated Wilson census. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileReportingWindow
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open OPE.Therm RG05Readout Address Native Pulse MergeProof Accent
open PhysicalNext.Repeat.Legato RGComparison.Core16.Spool WilsonReportingPlaquetteWindows
open WilsonPositionSeparatedProfileReportingCut WilsonReportingRegisteredWindows
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [DecidableEq I] (D : I→ℕ)

abbrev blocks (k per t:ℕ):=placements (V:=I) R.family k per t × rows R D

def fault (k per t : ℕ) (w : blocks R D k per t→ℂ)
    (cells : blocks R D k per t→I→Finset (Face (Per (R.family.side k per)))) (U:Config G (R.family.side k per)) : ℂ :=
  ∑a:blocks R D k per t,(⋃i,(House.chilly (cells a i) (cool R.family.path.levels k))ᶜ).indicator
    (fun V=>w a*∏i,(R.family.localSection (D i)).places (Pi.single (a.2 i) 1) (a.1.val i) V) U

theorem funded {k N : ℕ} (per t : ℕ) (live : k≤N) (w : blocks R D k per t→ℂ)
    (cells : blocks R D k per t→I→Finset (Face (Per (R.family.side k per)))) :
    Integrable (fun U=>(R.family.path.rep N per k).eval U • fault R D k per t w cells U) (prior G _) := by
  let A:=blocks R D k per t
  let J (a : A) (i : I) : Lamp G:=investment (R.makes.sections (D i)) (CoefficientBridge.run_valuation R (D i)) (a.2 i)
  let X (a : A):=tally (J a) a.1.val
  let E (a : A) : Set (Config G (R.family.side k per)) :=⋃i,(House.chilly (cells a i) (cool R.family.path.levels k))ᶜ
  let μ:=prior G (R.family.side k per)
  let weight := (R.family.path.rep N per k).eval
  have event (a:A):MeasurableSet (E a):=MeasurableSet.iUnion (fun i=>(House.bath (G:=G) _).compl)
  have raw (a:A):Integrable (fun U=>weight U • X a U) μ := by
    have earned:=actualTransport_weighted_integrable R.family R.makes live
      (tally_cont (J a) a.1.val).aestronglyMeasurable (WilsonRegisteredWindowRestriction.word (J a) a.1.val) le_rfl
    rwa [actualTransport_base R.family R.makes live] at earned
  have each (a:A):Integrable ((E a).indicator (fun U=>w a*(weight U • X a U))) μ:=((raw a).const_mul (w a)).indicator (event a)
  refine (integrable_finsetSum univ (fun a _=>each a)).congr (ae_of_all _ (fun U=>?_))
  change (∑a:A,(E a).indicator (fun V=>w a*(weight V • X a V)) U)=
    weight U • (∑a:A,(E a).indicator (fun V=>w a*X a V) U)
  rw [Finset.smul_sum]
  apply sum_congr rfl;intro a _
  by_cases good:U∈E a
  · simp only [Set.indicator_of_mem good,Complex.real_smul,mul_left_comm]
  · simp [good]

/-- Entire rough signed registered row, carried from its authentic reporting
law to any earlier census without worsening the coupling power. -/
theorem tested (stoves : Poetry R.family.path.levels) (simple : G.Simple) (φ : Wave I)
    (compact : HasCompactSupport φ.val) (d s e q : ℕ) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ k:ℕ in atTop,∀N per, k≤N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta k^s→
      ∀(y:(i:I)→R.family.label (D i)),(∀i b,‖y i b‖≤R.family.path.levels.clock.hatBeta k^e)→
      ∀(r:ℝ)(ξ:Cloud I)(cells:blocks R D k per t→I→Finset (Face (Per (R.family.side k per)))),
        (∀a i,((cells a i).card:ℝ)≤R.family.path.levels.clock.hatBeta k^d)→
        ∀{n u:ℕ}(date:n+1≤k)(span:u≤n)(g:Body),
        let w:=fun a:blocks R D k per t=>φ.val (fun i=>r⁻¹ • (R.family.S.place (a.1.val i)-ξ i))*price R D k N per y a.2
        (∫V,‖field R.family N per date span (fault R D k per t w cells) g V‖ ∂scene R.family.path N per u)≤
          ε*Pert.Asymptotics.regulatorRun R.family N per k^q := by
  filter_upwards [WilsonReportingRegisteredWindows.tested R D stoves simple φ compact d s e q ep] with k bill
  intro N per live t width y weights r ξ cells size n u date span g w
  exact (WilsonPositionSeparatedProfileReportingVariation.original R.family R.makes N per live date span _
    (funded R D per t live w cells) g).trans (bill N per live t width y weights r ξ cells size)

end YM.Integration.WilsonPositionSeparatedProfileReportingWindow
