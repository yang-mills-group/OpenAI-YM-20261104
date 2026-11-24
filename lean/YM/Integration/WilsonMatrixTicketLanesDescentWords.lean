import YM.Integration.WilsonMatrixTicketLanesDescentPrincipal
import YM.Integration.WilsonCoefficientPreparation
import YM.RGComparison.Core16.Insertions
import YM.RGComparison.Core16.Spool.Beacon

/-! Bare leading coefficients of actual mixed marked Wilson words on the whole descent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesDescentWords
open Function Filter Lattice RG Tree Wilson Precision Push.BetaTransport
open PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Series Tested Radial GaussianScore
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool
open scoped Topology ContDiff BigOperators Classical

variable {G : Gauge} (R : Run G) {ι : Type} [Fintype ι] (k : ι → ℕ)
    (i : (s : ι) → (R.family.labels.level (k s)).Index)

/-- The rows of the common original run at every named insertion. -/
def lamps (s : ι) : Lamp G :=
  investment (R.makes.sections (k s)) (CoefficientBridge.run_valuation R (k s)) (i s)

variable {N p : ℕ} {c : Side} (d : Descent (R.family.side N p) c)
    (x : ι → Site (R.family.side N p))

def word (b : Bool) : Config G (R.family.side N p) → ℝ := look b ∘ tally (lamps R k i) x

/-- Smoothness and the true bare order for a heterogeneous measured roster are
purchased by the run's retained local sections and their actual valuations. -/
theorem purchased (b : Bool) : d.Testable (word R k i x b) ∧
    d.grade (word R k i x b) (power (lamps R k i)) := by
  let F (s : ι) := (R.family.localSection (k s)).places (Pi.single (i s) 1) (x s)
  have entries (s : ι) : d.Testable (F s) ∧ d.grade (F s) ((R.family.labels.level (k s)).grades (i s)).2 :=
    basis_test R.makes (CoefficientBridge.run_valuation R (k s)) d (x s) (i s)
  refine ⟨⟨(look b).continuous.comp (tally_cont _ _),fun v U => congrArg (look b) (tally_invariant _ _ v U),?_⟩,?_⟩
  · have all : ContDiffAt ℝ ∞ (fun y : Coordinates G d => ∏ s, F s (d.fine 1 (d.tablePath y))) 0 :=
      contDiffAt_prod (fun s _ => (entries s).1.smooth)
    exact (look b).contDiff.contDiffAt.comp 0 all
  intro y
  let f (s : ι) (r : ℝ) := F s (d.fine 1 (d.tablePath (r • y)))
  have charged := bill_product Finset.univ (fun s => ((R.family.labels.level (k s)).grades (i s)).2)
    f (fun s _ => (entries s).2 y)
  obtain ⟨C,hC,ht⟩ := charged
  refine ⟨‖look b‖ * C,mul_nonneg (norm_nonneg _) hC,?_⟩
  filter_upwards [ht] with r cost
  have original : tally (lamps R k i) x (d.fine 1 (d.tablePath (r • y))) = (∏ s, f s) r := by
    rw [Finset.prod_apply]; rfl
  change ‖look b (tally (lamps R k i) x (d.fine 1 (d.tablePath (r • y))))‖ ≤ _
  rw [original]
  exact ((look b).le_opNorm _).trans ((mul_le_mul_of_nonneg_left cost (norm_nonneg _)).trans_eq (mul_assoc ..).symm)

/-- The genuine normalized finite Wilson conditional on the complete retained
descent tends to the Gaussian mean of its actual marked microscopic jet. -/
theorem original (P : ChartRatio G) (chart : LocalRatio P) (room : d.Room G)
    (t : d.Tags) (u : ℕ → ℝ) (b : Bool) :
    let f := word R k i x b
    let w := power (lamps R k i)
    let mean := (ambient t room).average (Chart.tangent G d.Links) (Radial.jet (f ∘ d.fine 1 ∘ d.tablePath) w)
    Tendsto (fun g : ℝ => g⁻¹^w * d.conditioned (offset u g) f 1) Tested.germ (𝓝 mean) ∧
      ranking P d u f w = mean := by
  intro f w mean
  obtain ⟨test,grade⟩ := purchased R k i d x b
  have first : ranking P d u f w = mean :=
    WilsonMatrixTicketLanesDescentPrincipal.gaussian P chart room t u test grade
  refine ⟨?_,first⟩
  rw [← first]
  simpa only [Nat.add_zero] using! ((rescaled_formula P chart room u test grade).tendsto_first)

end YM.Integration.WilsonMatrixTicketLanesDescentWords
