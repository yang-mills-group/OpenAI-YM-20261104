import YM.Integration.ActualRunStationaryCost
import YM.Integration.ScatterAnchoredSum
import YM.Comparison.RG02.Bulk.Square

/-! The original complete main-plus-noise score in physical Array coordinates.
The constants are selected before the level, cutoff, period, forest and tag.
The spatial coordinate factor remains explicit; no coordinate cardinality or
unpaid scalar estimate is substituted for the native Scatter receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunStationaryTensor

open Filter Function Set Metric Lattice RG Precision Tree
open Push.Uniform Comparison.RG02
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical ContDiff

section Native
variable {G : Gauge} {c f : Side} {S : StepData c f}
    (B : Forest S.ratio) (t : S.Choices)
    {P : PathData G} {p : Clip} {n : ℕ}
    {μ C Λ Z X K D δ W η : ℝ}

/-- The full native score has a normalized marginal at every fixed port. -/
theorem priced_marginal (hP : P.Bounds p μ C Λ)
    (hS : S.patch.Branches S.kernel G) (hn : 2 ≤ n)
    (hp : PaintSupply G (n + 1) Z) (hQ : SquarePay G n Z μ C X)
    (hE : ExpReceipt G (n + 1) K) (hL : LogReceipt G D δ)
    (hF : FocusReceipt G n W η) :
    ContDiffAt ℝ ω (priced B t p P) 0 ∧
      ∀ k : ℕ, k + 1 ≤ n → ∀ j : Fin (k + 1), ∀ i0 : Push.Uniform.Joint B G,
        (∑ q : Fin k → Push.Uniform.Joint B G,
          ‖(((k + 1).factorial : ℝ)⁻¹) •
            entry (priced B t p P) 0 (Fin.insertNth j i0 q)‖) ≤
          allCost G n Z X μ C K W p S.patch S.kernel *
            ((townCost G : ℝ) * countCost (weaker n (entryWidth n S.patch.L μ))) ^ k := by
  have H := paid_ball B t hP hS hn hp hQ hE hL hF
  have hz : (0 : Positions (Push.Uniform.Joint B G)) ∈
      ball 0 (paidRadius G n Z K D δ η S.patch S.kernel) := mem_ball_self H.1
  have h0 := H.2 0 hz
  refine ⟨h0.1, ?_⟩
  intro k hk j i0
  have hr := width_positive hP.width n S.patch.L
  have hw : 0 < weaker n (entryWidth n S.patch.L μ) := by
    unfold weaker
    positivity
  have hc : 0 ≤ allCost G n Z X μ C K W p S.patch S.kernel := by
    unfold allCost
    positivity
  exact ScatterAnchoredSum.normalized h0.2.1 (town B) hw hc hk j i0

end Native

/-- On the original Run, the complete score is paid by the original logarithmic
stamp and its explicit spatial coordinate factor. The native analytic receipts
are constructed from G and n before choosing the level, cutoff or period. -/
theorem surface_marginal {G : Gauge} (T : Run G)
    (hT : ActualRunNativeComponentRecipe.Attached T) (n : ℕ) (hn : 2 ≤ n) :
    let a := T.family.path.levels
    ∃ A : ℝ, 0 < A ∧ ∃ d : ℕ,
      ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i + 1 ≤ N →
        let S := a.clock.op i period
        let Y := a.params (i + 1)
        let μ := NativeCappedPathBounds.cappedWidth Y.width (a.clock.J (i + 1))
        ∀ (B : Forest S.ratio) (t : S.Choices),
          let F := Bulk.Surface S Y.clip
            (T.family.path.rep N period (i + 1)).path B t ∘ paint B G
          ContDiffAt ℝ ω F 0 ∧
            ∀ k : ℕ, k + 1 ≤ n → ∀ j : Fin (k + 1), ∀ i0 : Push.Uniform.Joint B G,
              (∑ q : Fin k → Push.Uniform.Joint B G,
                ‖(((k + 1).factorial : ℝ)⁻¹) •
                  entry F 0 (Fin.insertNth j i0 q)‖) ≤
                (A * (Real.log (a.clock.hatBeta i)) ^ d) *
                  ((townCost G : ℝ) * countCost
                    (weaker n (entryWidth n S.patch.L μ))) ^ k := by
  dsimp only
  let a := T.family.path.levels
  obtain ⟨Z, hp⟩ := paint_supply G (n + 1)
  obtain ⟨K, _hK, hE⟩ := exp_receipt G (n + 1)
  obtain ⟨D, δ, hL⟩ := log_receipt G
  obtain ⟨W, η, _hW, hF⟩ := focus_receipt G n
  obtain ⟨A, hA, d, H⟩ :=
    ActualRunStationaryCost.stationary_log_cost T hT n Z K W
  refine ⟨A, hA, d, ?_⟩
  filter_upwards [H] with i hi
  intro N period hN B t
  have h := hi N period hN
  have hscore := priced_marginal B t h.1 (a.blocks i period).branches
    hn hp h.2.1 hE hL hF
  refine ⟨hscore.1, ?_⟩
  intro k hk j i0
  have hr := width_positive h.1.width n (a.clock.op i period).patch.L
  have hw : 0 < weaker n (entryWidth n (a.clock.op i period).patch.L
      (NativeCappedPathBounds.cappedWidth (a.params (i + 1)).width
        (a.clock.J (i + 1)))) := by
    unfold weaker
    positivity
  exact (hscore.2 k hk j i0).trans
    (mul_le_mul_of_nonneg_right h.2.2
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (count_pos hw).le) k))

end YM.Integration.ActualRunStationaryTensor
end
