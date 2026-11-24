import YM.Integration.WilsonPositionSeparatedProfileReportingPrimary
import YM.Integration.WilsonPositionSeparatedProfileReportingError
import YM.Integration.WilsonReportingFittedWindows

/-! Removing the failed footprints at the original reporting date costs an
arbitrary power for the whole fitted physical roster at every earlier census. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileFittedPrimary
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open OPE.Therm RG05Readout Address Native Pulse MergeProof Accent
open PhysicalNext.Repeat.Legato WilsonReportingPlaquetteWindows WilsonReportingRegisteredWindows
open WilsonPositionSeparatedProfileReportingPrimary WilsonPositionSeparatedProfileReportingWindow
open WilsonPositionSeparatedProfileReportingCut
open private subtract from YM.Integration.WilsonPositionSeparatedProfileReportingError
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [DecidableEq I]

private theorem read_funded (D : I→ℕ) {k N : ℕ} (per t : ℕ) (live : k≤N)
    (y : (i:I)→R.family.label (D i)) (φ:Wave I) (r:ℝ) (ξ:Cloud I) :
    Integrable (fun U=>(R.family.path.rep N per k).eval U • read R D k N per t y φ r ξ U) (prior G _) := by
  have smooth : Continuous (read R D k N per t y φ r ξ) := by
    apply continuous_finsetSum; intro z _
    apply Continuous.mul continuous_const
    apply continuous_finsetProd; intro i _
    exact (R.family.localSection (D i)).continuous_places _ _
  obtain ⟨a,cap⟩:=isCompact_univ.exists_bound_of_continuousOn smooth.continuousOn
  have paid := actualTransport_weighted_integrable R.family R.makes live smooth.aestronglyMeasurable
    (fun U=>cap U (Set.mem_univ U)) le_rfl
  rwa [actualTransport_base R.family R.makes live] at paid

/-- Any authentic larger accepted plaquette patch can be used for a subsequent
local comparison. The finite sum defining `primary` keeps one common physical
configuration for all insertions. -/
theorem tested (stoves : Poetry R.family.path.levels) (simple : G.Simple) (D : I→ℕ)
    (ℓ : (i:I)→Letter (D i)) (φ : Wave I) (compact : HasCompactSupport φ.val) (d s q : ℕ)
    {ε:ℝ} (ep:0<ε) :
    ∀ᶠ k:ℕ in atTop, ∀ N per, k≤N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta k^s→
      ∀ (x:(i:I)→R.family.label (kept (ℓ i))) r ξ
        (cells:placements (V:=I) R.family k per t→I→Finset (Face (Per (R.family.side k per)))),
      (∀z i,cover ((R.family.localSection (kept (ℓ i))).footprint (z.val i))⊆cells z i)→
      (∀z i,((cells z i).card:ℝ)≤R.family.path.levels.clock.hatBeta k^d)→
      let e:=fun i=>kept (ℓ i)
      let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) k N per) (ℓ i)
      ∀(n u:ℕ)(date:n+1≤k)(span:u≤n)(g:Body),
        (∫V, ‖field R.family N per date span (read R e k N per t y φ r ξ) g V-
          field R.family N per date span (primary R e k N per t y φ r ξ cells) g V‖ ∂scene R.family.path N per u)≤
          (∏i,mass R.family (e i) (x i))*(ε*Pert.Asymptotics.regulatorRun R.family N per k^q) := by
  let e:=fun i=>kept (ℓ i)
  have ages : ∀ᶠ k : ℕ in atTop, ∀i,R.family.ref (e i)≤k ∧ R.family.ref (D i)≤k:=
    eventually_all.mpr (fun i=>(eventually_ge_atTop _).and (eventually_ge_atTop _))
  filter_upwards [WilsonReportingFittedWindows.original R stoves simple D ℓ φ compact d s q ep,
    OPE.Therm.narrow (H:=R.family.path) simple,ages] with k bill cold old N per live t radius x r ξ cells inside plenty
  dsimp only
  intro n u date span g
  let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) k N per) (ℓ i)
  let F:=read R e k N per t y φ r ξ
  let H:=primary R e k N per t y φ r ξ cells
  let w : blocks R e k per t→ℂ:=fun a=>φ.val (fun i=>r⁻¹ • (R.family.S.place (a.1.val i)-ξ i))*price R e k N per y a.2
  let A:=fault R e k per t w (fun a=>cells a.1)
  have ceiling : cool R.family.path.levels k≤(R.family.path.rep N per k).p.threshold:=by
    have align : (R.family.path.rep N per k).p=R.family.path.levels.budget k:=(R.makes.wilson.represents N per k live).vac
    rw [align]
    change cool R.family.path.levels k≤R.family.path.levels.clock.threshold k
    linarith only [cold.1,cold.2]
  have diff : F-H=A:=funext (compared R e k N per t y φ r ξ cells inside ceiling)
  let μ:=prior G (R.family.side k per)
  let weight:=(R.family.path.rep N per k).eval
  have f:Integrable (fun U=>weight U • F U) μ:=read_funded R e per t live y φ r ξ
  have a:Integrable (fun U=>weight U • A U) μ:=funded R e per t live w _
  have h:Integrable (fun U=>weight U • H U) μ:=by
    refine (f.sub a).congr (ae_of_all _ (fun U=>?_))
    change weight U • F U - weight U • A U = weight U • H U
    rw [←smul_sub,← diff,Pi.sub_apply,sub_sub_cancel]
  have fd:Integrable (fun U=>weight U • (F-H) U) μ:=diff ▸ a
  have bound:=WilsonPositionSeparatedProfileReportingVariation.original R.family R.makes N per live date span (F-H) fd g
  rw [subtract R.family N per date span F H f h g,diff] at bound
  exact bound.trans (bill N per live t radius old x r ξ (fun a=>cells a.1) (fun a i=>plenty a.1 i))

/-- The original footprint itself has a fixed, period-independent face cost,
so the fitted comparison has no auxiliary chamber hypothesis. -/
theorem original (stoves : Poetry R.family.path.levels) (simple : G.Simple) (D : I→ℕ)
    (ℓ:(i:I)→Letter (D i)) (φ:Wave I) (compact:HasCompactSupport φ.val) (s q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ k:ℕ in atTop,∀N per,k≤N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta k^s→
      ∀(x:(i:I)→R.family.label (kept (ℓ i))) r ξ,
      let e:=fun i=>kept (ℓ i)
      let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) k N per) (ℓ i)
      let cells:=fun (z:placements (V:=I) R.family k per t) i=>cover ((R.family.localSection (e i)).footprint (z.val i))
      ∀(n u:ℕ)(date:n+1≤k)(span:u≤n)(g:Body),
        (∫V, ‖field R.family N per date span (read R e k N per t y φ r ξ) g V-
          field R.family N per date span (primary R e k N per t y φ r ξ cells) g V‖ ∂scene R.family.path N per u)≤
          (∏i,mass R.family (e i) (x i))*(ε*Pert.Asymptotics.regulatorRun R.family N per k^q) := by
  let bound (i:I):ℕ:=(R.family.localSection (kept (ℓ i))).stencil.card*5^4*Fintype.card PlaqAxes
  have rate:∀ᶠ k:ℕ in atTop,∀i,(bound i:ℝ)≤R.family.path.levels.clock.hatBeta k:=
    eventually_all.mpr (fun i=>(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (bound i))
  filter_upwards [WilsonPositionSeparatedProfileFittedPrimary.tested R stoves simple D ℓ φ compact 1 s q ep,rate] with k granted wide N per live t radius x r ξ
  apply granted N per live t radius x r ξ _ (fun _ _=>Finset.Subset.refl _)
  intro z i
  rw [pow_one]
  exact le_trans (by exact_mod_cast footprint R (kept (ℓ i)) (z.val i) : _≤(bound i:ℝ)) (wide i)

end YM.Integration.WilsonPositionSeparatedProfileFittedPrimary
