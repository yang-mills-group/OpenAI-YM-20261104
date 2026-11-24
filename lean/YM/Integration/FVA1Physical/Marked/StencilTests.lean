import YM.Qlocal.Quipu.Crust

/-! Independent signed tests on the individual countable terms of a marked
physical stencil. Testing preserves its gauge invariance, source geometry,
and full exponential price. Its realized polynomial uses those very tests. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice Wilson RG Qlocal Qlocal.Quipu Quipu.Sonnet Tern Push.AbsoluteSums
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {B : Marker.Census V} {G : Gauge}
variable {ξ : V → ℕ} {qd n : ℕ} {s : Senses B}

/-- An independently chosen signed scalar at every marker, perturbative order,
rank, and countable source label. -/
abbrev StencilTests (B : Marker.Census V) (ξ : V → ℕ) (qd : ℕ) :=
  ∀ (s : Senses B) (e : Fin (qd + 1)),
    Fin (e.val + Lagger.dues ξ s.val + 1) → ℕ → Set.Icc (-1 : ℝ) 1

/-- Independent tests at each occupied source slot, assembled on its actual mask. -/
def slotTests (t : V → StencilTests B ξ qd) : StencilTests B ξ qd := fun s e n j =>
  ⟨∏ v ∈ s.val.val, (t v s e n j : ℝ), by
    apply abs_le.mp
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun v _ => abs_le.mpr (t v s e n j).property)⟩

/-- Change only the invariant tensor coefficient of the marked term. -/
def testVase (u : ℝ) (A : Vase s G n) : Vase s G n :=
  { A with ink := u • A.ink, legal := (Stationary.paints G n).smul_mem u A.legal }

theorem testVase_fare (u a : ℝ) (A : Vase s G n) :
    (testVase u A).fare a = |u| * A.fare a := by
  change (∑ i, |u * A.ink i|) * Real.exp (a * A.momentum) = _
  simp only [abs_mul, ← Finset.mul_sum, Vase.fare, Vase.sizeC, mul_assoc]

theorem testVase_read (u : ℝ) (A : Vase s G n) {c : Side} (o : Site c) (j : ℕ)
    (field : Config G c) : (testVase u A).read o j field = u * A.read o j field := by
  unfold Vase.read Vase.draw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (u * A.ink i) * _ = u * (A.ink i * _)
  exact mul_assoc _ _ _

def testedStencil (A : Stanza B G ξ qd) (t : StencilTests B ξ qd) : Stanza B G ξ qd :=
  fun s e n j => testVase (t s e n j) (A s e n j)

/-- A fixed source envelope pays simultaneously for every collection of
independent signed tests. The admissible geometry and the depth are identical. -/
theorem testedStencil_allows (A : Stanza B G ξ qd) (t : StencilTests B ξ qd)
    {b : ℕ} {a C : ℝ} (h : (Stanza.son A b).Allows a C) :
    (Stanza.son (testedStencil A t) b).Allows a C := by
  constructor
  intro s e n
  exact budget_mono (h.pay s e n) (fun j => by
    rw [show (Stanza.son (testedStencil A t) b).array s e n j =
      testVase (t s e n j) (A s e n j) from rfl, testVase_fare]
    exact mul_nonneg (abs_nonneg _) ((h.pay s e n).1 j)) (fun j => by
    rw [show (Stanza.son (testedStencil A t) b).array s e n j =
      testVase (t s e n j) (A s e n j) from rfl, testVase_fare]
    exact mul_le_of_le_one_left ((h.pay s e n).1 j) (abs_le.mpr (t s e n j).property))

/-- The admitted mask and rooted geometry are kept in every summand. Reading the
tested physical stencil gives the signed sum of the original physical readings. -/
theorem testedStencil_read (A : Stanza B G ξ qd) (t : StencilTests B ξ qd) (b : ℕ)
    (mask : (Stanza.son A b).Decision) {c : Side} (o : V → Site c) (s : Senses B)
    (e : Fin (qd + 1)) (n : Fin (e.val + Lagger.dues ξ s.val + 1)) (field : Config G c) :
    (Stanza.son (testedStencil A t) b).playing mask o s e n field =
      ∑' j : ℕ, (t s e n j : ℝ) *
        (if mask s e n j ∧ (A s e n j).stage.Hears o then
          (A s e n j).read (o (Sonnet.root s)) b field else 0) := by
  unfold Tale.playing Album.picture Album.realize
  apply tsum_congr
  intro j
  unfold Album.readout
  rw [show ((testedStencil A t).son b).array s e n j = testVase (t s e n j) (A s e n j) from rfl,
    show ((testedStencil A t).son b).method = b from rfl]
  split_ifs with tested original original
  · exact testVase_read _ _ _ _ _
  · exact (original tested).elim
  · exact (tested original).elim
  · exact (mul_zero (t s e n j : ℝ)).symm

theorem testedStencil_summable (A : Stanza B G ξ qd) (t : StencilTests B ξ qd) (b : ℕ)
    {a C : ℝ} (ha : 0 < a) (hA : (Stanza.son A b).Allows a C)
    (mask : (Stanza.son A b).Decision) {c : Side} (o : V → Site c) (s : Senses B)
    (e : Fin (qd + 1)) (n : Fin (e.val + Lagger.dues ξ s.val + 1)) (field : Config G c) :
    Summable (fun j : ℕ => (t s e n j : ℝ) *
      (if mask s e n j ∧ (A s e n j).stage.Hears o then
        (A s e n j).read (o (Sonnet.root s)) b field else 0)) := by
  apply Summable.of_norm_bounded ((hA.pay s e n).2.1.mul_left (Vase.ticketC G b n.val))
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  apply (mul_le_of_le_one_left (abs_nonneg _) (abs_le.mpr (t s e n j).property)).trans
  split_ifs
  · exact (A s e n j).paid (o (Sonnet.root s)) field ha b
  · rw [abs_zero]
    exact mul_nonneg (Vase.ticketC_pos ..) ((hA.pay s e n).1 j)

/-- Linear dependence on each independently tagged input term continues to hold
after the physical read and unconditional summation. -/
theorem testedStencil_read_add (A : Stanza B G ξ qd) (t₁ t₂ t₃ : StencilTests B ξ qd)
    (b : ℕ) {a C : ℝ} (ha : 0 < a) (hA : (Stanza.son A b).Allows a C)
    (mask : (Stanza.son A b).Decision) {c : Side} (o : V → Site c) (s : Senses B)
    (e : Fin (qd + 1)) (n : Fin (e.val + Lagger.dues ξ s.val + 1)) (field : Config G c)
    (ht : ∀ j, (t₃ s e n j : ℝ) = t₁ s e n j + t₂ s e n j) :
    (Stanza.son (testedStencil A t₃) b).playing mask o s e n field =
      (Stanza.son (testedStencil A t₁) b).playing mask o s e n field +
      (Stanza.son (testedStencil A t₂) b).playing mask o s e n field := by
  rw [testedStencil_read, testedStencil_read, testedStencil_read,
    ← (testedStencil_summable A t₁ b ha hA mask o s e n field).tsum_add
      (testedStencil_summable A t₂ b ha hA mask o s e n field)]
  exact tsum_congr fun j => by rw [ht j, add_mul]

end YM.Integration.FVA1Physical.Marked
