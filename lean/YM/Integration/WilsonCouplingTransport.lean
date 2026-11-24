import YM.Integration.ActualSignedCore

/-! A finite original Wilson lattice at varying bare and blocking couplings.
Every station uses the same clock, paths, branch probabilities, and Haar priors. -/
noncomputable section
namespace YM.Integration.WilsonCouplingTransport
open YM MeasureTheory Lattice Wilson RG MergeProof.Accent Extra.Trajectories
variable {G : Gauge} (C : Family G) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterate the original conditional kernels at a supplied schedule of real
inverse couplings on this finite lattice. -/
def carry (p j : ℕ) (β : ℕ → ℝ) (x : Config G (C.side j p) → E) (i : ℕ) (hi : i ≤ j) :
    Config G (C.side i p) → E :=
  Nat.decreasingInduction (motive := fun m _ => Config G (C.side m p) → E)
    (fun m _ v => (C.path.levels.clock.op m p).push (β (m+1)) v) x hi

theorem top (p j : ℕ) (β : ℕ → ℝ) (x : Config G (C.side j p) → E) :
    carry C p j β x j le_rfl = x := Nat.decreasingInduction_self ..

theorem step (p j : ℕ) (β : ℕ → ℝ) (x : Config G (C.side j p) → E) {i : ℕ} (hi : i < j) :
    carry C p j β x i hi.le =
      (C.path.levels.clock.op i p).push (β (i+1)) (carry C p j β x (i+1) hi) :=
  Nat.decreasingInduction_succ_left ..

theorem integrable (p j : ℕ) (β : ℕ → ℝ) {x : Config G (C.side j p) → E}
    (hx : Integrable x (prior G _)) {i : ℕ} (hi : i ≤ j) :
    Integrable (carry C p j β x i hi) (prior G _) := by
  induction hi using Nat.decreasingInduction with
  | self => rwa [top]
  | of_succ m hm ih =>
    rw [step C p j β x hm]
    exact StepData.push_integrable (C.path.levels.transition_mass ..) _ ih

theorem integral [CompleteSpace E] (p j : ℕ) (β : ℕ → ℝ) {x : Config G (C.side j p) → E}
    (hx : Integrable x (prior G _)) {i : ℕ} (hi : i ≤ j) :
    (∫ U, carry C p j β x i hi U ∂prior G _) = ∫ U, x U ∂prior G _ := by
  induction hi using Nat.decreasingInduction with
  | self => rw [top]
  | of_succ m hm ih =>
    rw [step C p j β x hm, StepData.push_integral (C.path.levels.transition_mass ..) _
      (integrable C p j β hx hm), ih]

/-- At the actual funded schedule the whole transported signed numerator is
definitionally the original Wilson push, including at intermediate levels. -/
theorem physical (N p j : ℕ) (x : Config G (C.side j p) → E) {i : ℕ} (hi : i ≤ j) :
    carry C p j (C.path.β N p) x i hi = gust C.path N p j x i hi := rfl

def density (N p : ℕ) (b : ℝ) (β : ℕ → ℝ) (i : ℕ) (hi : i ≤ N) :
    Config G (C.side i p) → ℝ := carry C p N β (bare b) i hi

/-- All cutoff and period dependent normalizations of the original trajectory
are recovered when the couplings are specialized. -/
theorem physical_density (H : C.Makes) (N p : ℕ) {i : ℕ} (hi : i ≤ N) :
    density C N p (C.beta N p) (C.path.β N p) i hi = (C.path.rep N p i).eval := by
  change carry C p N _ (bare _) i hi = _
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [top]
    exact (H.wilson.starts N p).2.symm
  | of_succ m hm ih =>
    rw [step C p N _ _ hm, ih]
    exact (H.wilson.steps N p m hm).1.symm

/-- The finite partition depends only on the varying bare coupling, even when
every blocking coupling varies independently and all sites are retained. -/
theorem partition_at (N p : ℕ) (b : ℝ) (β : ℕ → ℝ) {i : ℕ} (hi : i ≤ N) :
    (∫ U, density C N p b β i hi U ∂prior G _) = partition G (C.side N p) b :=
  integral C p N β (bare_integrable b) hi

/-- The original normalized scalar or vector-valued Wilson numerator at the
bare inverse coupling is recovered by every intermediate station. -/
theorem signed_moment [CompleteSpace E] (N p : ℕ) (b : ℝ) (β : ℕ → ℝ)
    (x : Config G (C.side N p) → E) (hx : Integrable (fun U => bare b U • x U) (prior G _))
    {i : ℕ} (hi : i ≤ N) :
    (∫ U, density C N p b β i hi U ∂prior G _)⁻¹ •
      (∫ U, carry C p N β (fun V => bare b V • x V) i hi U ∂prior G _) =
      (partition G (C.side N p) b)⁻¹ • ∫ U, bare b U • x U ∂prior G _ := by
  rw [partition_at, integral C p N β hx hi]

end YM.Integration.WilsonCouplingTransport
