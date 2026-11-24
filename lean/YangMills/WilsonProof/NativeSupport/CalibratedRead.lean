import YangMills.WilsonProof.NativeSupport.CalibratedTerminal
import YangMills.WilsonProof.NativeSupport.LayerPressure

/-! A real packet moment is a coefficient of the calibrated marker tape on
the very same original traversal, including its evaluated denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open Function Finset MeasureTheory Lattice RG Wilson Marker
open MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance
open scoped Classical BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : Gauge}

private lemma seed_cont {n : Side} (B : Census V) (R : Rep G n) (hR : Continuous R.eval)
    (F : V → Config G n → ℝ) (hF : ∀ i, Continuous (F i)) :
    Continuous (birth B R (fun i U => (F i U : ℂ))) := by
  apply (Complex.continuous_ofReal.comp hR).smul
  apply Poly.pass_cont.comp
  apply continuous_finsetSum
  intro i _
  apply continuous_pi
  intro j
  change Continuous (fun a => (Poly.send (B.fire i) (F i a : ℂ)).part j)
  simp_rw [Poly.part_send]
  split_ifs
  · exact Complex.continuous_ofReal.comp (hF i)
  · exact continuous_const

omit [Fintype V] [DecidableEq V] in
private lemma push_real {f c : Side} (S : StepData c f) (β : ℝ)
    (g : Config G f → ℝ) :
    S.push β (Complex.ofReal ∘ g) = Complex.ofReal ∘ S.push β g := by
  funext x
  unfold StepData.push
  simp_rw [comp_apply, Complex.real_smul, smul_eq_mul, ← Complex.ofReal_mul, integral_complex_ofReal]

private lemma actual_part (A : History G) (selected : A.Selected) {N p k : ℕ}
    (T : Slices A.levels p) (hk : k ≤ N) (B : Census V)
    (F : V → Config G (A.S.side N p) → ℝ) (hF : ∀ i, Continuous (F i)) (s : B.Mode) :
    (fun U => (gust A N p N (birth B (A.rep N p N) (fun i U => (F i U : ℂ))) k hk U).part s) =
      Complex.ofReal ∘ (traversal T hk).weighted (RGComparison.Core16.line A p k N)
        (fun U => ∏ i ∈ s.val, F i U) := by
  let seed := birth B (A.rep N p N) (fun i U => (F i U : ℂ))
  have hR : Continuous (A.rep N p N).eval := (selected.starts N p).2.symm ▸ bare_cont _
  have integ : Integrable seed (prior G _) :=
    (seed_cont B _ hR F hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  induction hk using Nat.decreasingInduction with
  | self =>
    rw [gust_base, traversal_self, Descent.weighted, Descent.output_nil]
    funext U
    simp only [birth, Poly.part_smul, Mach, pass_fire, (selected.starts N p).2,
      comp_apply, smul_eq_mul]
    change _ = ((bare (A.β N p (N+0)) U * (∏ i ∈ s.val, F i U) : ℝ) : ℂ)
    rw [Nat.add_zero, Complex.ofReal_mul, Complex.ofReal_prod]
  | of_succ k hk ih =>
    rw [gust_step A N p N seed hk, weighted_step T _ hk]
    rw [push_get (A.levels.transition_mass ..) (gust_live A N p N seed integ hk) s, ih, push_real]

theorem calibrated_submoment (A : History G) (selected : A.Selected) {N p k : ℕ}
    (T : Slices A.levels p) (hk : k ≤ N) (B : Census V)
    (F : V → Config G (A.S.side N p) → ℝ) (hF : ∀ i, Continuous (F i))
    (sym : ∀ i, GaugeInvariant (F i)) (s : B.Mode) (U : Config G (A.S.side k p)) :
    let X := gust A N p N (birth B (A.rep N p N) (fun i U => (F i U : ℂ))) k hk U
    let d := traversal T hk
    let β := RGComparison.Core16.line A p k N
    ((X.part B.quiet)⁻¹ • X).part s =
      ((mass d β (fun U => ∏ i ∈ s.val, F i U) U / mass d β 1 U : ℝ) : ℂ) := by
  intro X d β
  let f (U : Config G (A.S.side N p)) := ∏ i ∈ s.val, F i U
  have neat : Continuous f := continuous_finsetProd _ fun i _ => hF i
  have turns : GaugeInvariant f := fun g U => Finset.prod_congr rfl fun i _ => sym i g U
  have quiet : X.part B.quiet = (d.vacuum β U : ℂ) := by
    have h := congrFun (actual_part A selected T hk B F hF B.quiet) U
    rw [← Descent.weighted_unit]
    simpa only [X,d,β, Census.quiet, prod_empty, comp_apply, Pi.one_def] using h
  have at_s : X.part s = ((d.weighted β f U : ℝ) : ℂ) :=
    congrFun (actual_part A selected T hk B F hF s) U
  rw [Poly.part_smul, quiet, at_s, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (fraction d (traversal_ok T hk) β U neat turns)

end YM.Integration.InletSusceptibility
