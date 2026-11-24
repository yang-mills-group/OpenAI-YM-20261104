import YM.Integration.WilsonRegisteredWindowRestriction
import YM.OPE.Therm.Bath
import YM.Pert.Asymptotics.RawAxis

/-! On the original positive Wilson run, the exceptional part of a signed
finite stencil sum costs an arbitrarily high power of its actual coupling.
Each occupied term may choose its own region of plaquettes after the cutoff,
period, and translated sites are fixed. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredPlaquetteReading
open Filter MeasureTheory Lattice Wilson RG OPE.Therm RGComparison.Core16.Spool
open WilsonRegisteredWindowRestriction
open scoped BigOperators Classical Topology
variable {G : Gauge}

/-- A polynomial count of local plaquettes is paid at the measured coupling. -/
theorem currency (C : Family G) (hC : C.Makes) (simple : G.Simple) (d q : ℕ)
    {η : ℝ} (ep : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N →
      C.path.levels.clock.hatBeta k ^ d * vanishP C.path.levels k ≤
        η * Pert.Asymptotics.regulatorRun C N per k ^ q := by
  have decays := disappears (H := C.path) simple (d+q)
  have allowance : 0 < η/(2:ℝ)^q := div_pos ep (by positivity)
  filter_upwards [decays.eventually (gt_mem_nhds allowance)] with k small
  intro N per live
  let x := C.path.levels.clock.hatBeta k
  let y := C.path.β N per k
  have one : 1 ≤ x := (C.path.levels.fits.delayed k).le
  have xp : 0 < x := zero_lt_one.trans_le one
  have actual := (hC.wilson.represents N per k live).band
  have upper : y ≤ 2*x := actual.2
  have yp : 0 < y := (half_pos xp).trans_le actual.1
  have two : 0 < 2*x := mul_pos (by norm_num) xp
  have root : Real.sqrt y ≤ 2*x := (Real.sqrt_le_left two.le).mpr
    (upper.trans (by nlinarith only [mul_nonneg two.le (show 0 ≤ 2*x-1 by linarith only [one])]))
  have inv : (2*x)⁻¹ ≤ Pert.Asymptotics.regulatorRun C N per k :=
    inv_anti₀ (Real.sqrt_pos.mpr yp) root
  change x^(d+q)*vanishP C.path.levels k < η/2^q at small
  calc
    _ ≤ (η/2^q)/x^q := (le_div_iff₀ (pow_pos xp q)).mpr (by
      rw [pow_add] at small
      simpa only [mul_right_comm] using small.le)
    _ = η * ((2*x)⁻¹)^q := by rw [inv_pow, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr two.le) inv _) ep.le

/-- This uses the same original stove certificate that buys the measured
plaquette bound, without a separate independent formal field or a global
regularity event. The exact weighted stencil bill survives the signed sum. -/
theorem original (C : Family G) (hC : C.Makes) (stoves : Poetry C.path.levels) (simple : G.Simple)
    (d q : ℕ) {η : ℝ} (ep : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ N per j, j ≤ N → ∀ low : k ≤ j,
      ∀ {A I L : Type} [Fintype A] [Fintype I] [Fintype L]
        (J : A → L → Lamp G) (o : A → L → Site (C.side j per)) (w : A → ℂ)
        (cells : A → I → Finset (Face (Per (C.side k per)))),
      (∀ a i, ((cells a i).card : ℝ) ≤ C.path.levels.clock.hatBeta k ^ d) →
      ∫ V, ‖∑ a, (⋃ i, (House.chilly (cells a i) (cool C.path.levels k))ᶜ).indicator
        (fun U => w a * actualTransport C (N := N) (tally (J a) (o a)) low U) V‖
        ∂scene C.path N per k ≤
        ((Fintype.card I : ℝ) * (η * Pert.Asymptotics.regulatorRun C N per k^q)) *
          ∑ a, ‖w a‖ * wordBound (J a) := by
  filter_upwards [rare stoves simple hC.wilson, currency C hC simple d q ep] with k alarm pays
  intro N per j top low A I L _ _ _ J o w cells size
  have live := low.trans top
  letI : IsProbabilityMeasure (scene C.path N per k) := probability hC.wilson live
  apply bank C hC top low J o w (fun a i => (House.chilly (cells a i) (cool C.path.levels k))ᶜ)
  · exact fun a i => (House.bath (G := G) _).compl
  · intro a i
    apply (House.cool_miss (vanishP C.path.levels k) (alarm N live per) (cells a i)).trans
    exact (mul_le_mul_of_nonneg_right (size a i) (Real.exp_pos _).le).trans (pays N per live)

end YM.Integration.WilsonRegisteredPlaquetteReading
