import YM.Integration.LocalComparisonInterface

/-! Orientation of the original independent qlocal tests.
Complex conjugation preserves every real derivative norm and every original
Bill constant. The ambient Mood is only a submodule, so no extra norm on it
is introduced. The slotwise involution changes coordinates, not the family
of admissible tests. No commutation with a complex coefficient basis is used. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.QlocalOrientedTests
open Function ComparisonDensity.Address LocalComparison
open scoped ContDiff Classical

def conjugate (f : Pos → ℂ) : Pos → ℂ := fun x => star (f x)

/-- Pointwise conjugation preserves the full real derivative norm. -/
theorem conjugate_jet_norm (f : Pos → ℂ) (k : ℕ) (x : Pos) :
    ‖iteratedFDeriv ℝ k (conjugate f) x‖ = ‖iteratedFDeriv ℝ k f x‖ := by
  change ‖iteratedFDeriv ℝ k (Complex.conjLIE ∘ f) x‖ = _
  exact Complex.conjLIE.norm_iteratedFDeriv_comp_left f x k

theorem conjugate_involutive : Involutive conjugate := by
  intro f
  funext x
  exact star_star (f x)

/-- Both whole and cell Bills retain their literal order, weight and constant. -/
theorem bill_conjugate {U : Orbit} {f : Pos → ℂ} {c : ℝ}
    (h : U.Bill f c) : U.Bill (conjugate f) c := by
  refine ⟨h.nonneg, ?_, ?_⟩
  · change ContDiff ℝ (U.D : WithTop ℕ∞) (Complex.conjCLE ∘ f)
    exact Complex.conjCLE.contDiff.comp h.orders
  · intro k hk x hx
    rw [conjugate_jet_norm]
    exact h.limits k hk x hx

theorem bill_conjugate_iff (U : Orbit) (f : Pos → ℂ) (c : ℝ) :
    U.Bill (conjugate f) c ↔ U.Bill f c := by
  constructor
  · intro h
    simpa only [conjugate_involutive f] using bill_conjugate h
  · exact bill_conjugate

def conjugateMood (U : Orbit) (f : U.Mood) : U.Mood :=
  ⟨conjugate f.val, by
    obtain ⟨c, hc⟩ := f.property
    exact ⟨c, bill_conjugate hc⟩⟩

theorem conjugateMood_involutive (U : Orbit) :
    Involutive (conjugateMood U) := by
  intro f
  apply Subtype.ext
  exact conjugate_involutive f.val

theorem conjugateMood_add (U : Orbit) (f g : U.Mood) :
    conjugateMood U (f + g) = conjugateMood U f + conjugateMood U g := by
  apply Subtype.ext
  funext x
  exact star_add (f.val x) (g.val x)

theorem conjugateMood_smul (U : Orbit) (c : ℂ) (f : U.Mood) :
    conjugateMood U (c • f) = star c • conjugateMood U f := by
  apply Subtype.ext
  funext x
  change star (c * f.val x) = star c * star (f.val x)
  simp only [star_mul, mul_comm]

def orientedMood (U : Orbit) (flip : Bool) (f : U.Mood) : U.Mood :=
  if flip then conjugateMood U f else f

theorem orientedMood_involutive (U : Orbit) (flip : Bool) :
    Involutive (orientedMood U flip) := by
  cases flip
  · intro f; rfl
  · exact conjugateMood_involutive U

theorem orientedMood_add (U : Orbit) (flip : Bool) (f g : U.Mood) :
    orientedMood U flip (f + g) =
      orientedMood U flip f + orientedMood U flip g := by
  cases flip
  · rfl
  · exact conjugateMood_add U f g

theorem orientedMood_smul (U : Orbit) (flip : Bool) (c : ℂ) (f : U.Mood) :
    orientedMood U flip (c • f) =
      (if flip then star c else c) • orientedMood U flip f := by
  cases flip
  · rfl
  · exact conjugateMood_smul U c f

def moodEquiv (U : Orbit) (flip : Bool) : U.Mood ≃ U.Mood where
  toFun := orientedMood U flip
  invFun := orientedMood U flip
  left_inv := orientedMood_involutive U flip
  right_inv := orientedMood_involutive U flip

variable {V : Type} (D : V → Orbit) (flip : V → Bool)

def orientedTests (x : IndependentTests D) : IndependentTests D :=
  fun v => if flip v then ⟨conjugate (x v).val, bill_conjugate (x v).property⟩ else x v

theorem orientedTests_involutive : Involutive (orientedTests D flip) := by
  intro x
  funext v
  apply Subtype.ext
  cases h : flip v <;> simp [orientedTests, h]
  exact conjugate_involutive (x v).val

def testsEquiv : IndependentTests D ≃ IndependentTests D where
  toFun := orientedTests D flip
  invFun := orientedTests D flip
  left_inv := orientedTests_involutive D flip
  right_inv := orientedTests_involutive D flip

/-- The same oriented unit test is included in the original ambient slot. -/
theorem orientedTests_inclusion (x : IndependentTests D) :
    testInclusion D (orientedTests D flip x) =
      fun v => orientedMood (D v) (flip v) (testInclusion D x v) := by
  funext v
  apply Subtype.ext
  cases h : flip v <;>
    simp [orientedTests, orientedMood, testInclusion, conjugateMood, h]

/-- The orientation acts independently on every ambient test slot. -/
def orientedSpace (x : TestSpace D) : TestSpace D :=
  fun v => orientedMood (D v) (flip v) (x v)

theorem orientedSpace_involutive : Involutive (orientedSpace D flip) := by
  intro x
  funext v
  exact orientedMood_involutive (D v) (flip v) (x v)

/-- Pulling back an arbitrary full family and orienting the unit input
recovers the original family at the original independent tests. -/
theorem original_family {X : Type*} (F : TestSpace D → X)
    (x : IndependentTests D) :
    F (orientedSpace D flip (testInclusion D (orientedTests D flip x))) =
      F (testInclusion D x) := by
  rw [orientedTests_inclusion]
  exact congrArg F (orientedSpace_involutive D flip (testInclusion D x))

end YM.Integration.QlocalOrientedTests
