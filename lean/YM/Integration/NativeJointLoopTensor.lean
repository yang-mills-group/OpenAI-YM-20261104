import YM.Integration.ScatterAnchoredSum
import YM.Push.STATIONARY_UNIFORM.ScoreBounds
import YM.Extra.ITERATION_NO_LOSS.Sums

/-! The original full loop on the native nonlinear coarse/fine chart.
PathData.Bounds.two pays its rank-two atoms. The exact finite Signed average
is retained and its cardinality cancels; there is no spatial-volume factor.
The external coupling square and actual schedule payment remain separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeJointLoopTensor

open Function Filter Set Metric Lattice Wilson RG Precision Tree Exterior
open Push.Uniform
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {c f : Side} {ratio : Ratio c f} (B : Forest ratio)
variable {N : ℕ} {Z width C Λ : ℝ} {clip : Clip} {R : PathData G}

def loopCost (G : Gauge) (N : ℕ) (Z width Λ : ℝ) (L : Side) : ℝ :=
  Λ * atomCost G Z width N 2 * countCost (entryWidth N L width / 2)

/-- Analyticity and Scatter for the entire original symmetry-averaged loop. -/
theorem loop_beacons (H : R.Bounds clip width C Λ) (hs : PaintSupply G N Z)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1) :
    ContDiffAt ℝ ω (fun z => loop R (fine G B z)) x ∧
      Scatter (address B G) (weaker N (entryWidth N ratio.count width)) N
        (fun z => loop R (fine G B z)) x (loopCost G N Z width Λ ratio.count) := by
  let a := entryWidth N ratio.count width
  let M := Λ * atomCost G Z width N 2
  let u (s : Signed) (o : Site f) (z : Positions (Joint B G)) :=
    ∑' i : ℕ, (R.loop i).unmasked (signedFine B z s) o
  let F (s : Signed) (z : Positions (Joint B G)) := ∑ o, u s o z
  have hu (s : Signed) (o : Site f) : ContDiffAt ℝ ω (u s o) x :=
    label_analytic B R.loop H.width H.two s hs o x hx
  have hb (s : Signed) (o : Site f) : Beacon (address B G) a N
      (u s o) (affine s 0 o) x M :=
    atom_beacon B s H.width H.two hs x hx o
  have hF (s : Signed) : ContDiffAt ℝ ω (F s) x :=
    ContDiffAt.sum (s := Finset.univ) (fun o _ => hu s o)
  have hM : 0 ≤ M := mul_nonneg (Extra.Iteration.Cost.nonneg H.two) (atomCost_nn hs H.width 2)
  have ha := width_positive H.width N ratio.count
  have hscatter (s : Signed) : Scatter (address B G) (weaker N a) N (F s) x
      (M * countCost (a / 2)) := by
    have hi : Injective (affine (R := Per f) s 0) := by
      intro i j hij
      unfold affine at hij
      have he := add_right_cancel hij
      simpa using congrArg s⁻¹.act he
    have h := scatter (Multiplicity.injective hi) (fun o => hu s o) (fun o => hb s o) ha hM
    simpa only [Nat.cast_one, mul_one] using h
  let q : ℝ := Fintype.card Signed
  have hq : 0 < q := by unfold q; positivity
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun s _ => hF s)
  have he (z : Positions (Joint B G)) : loop R (fine G B z) = Patch.average (fun s => F s z) := rfl
  simp_rw [he, Patch.average]
  refine ⟨hsum.const_smul q⁻¹, ?_⟩
  have ht := (scatter_sum (s := Finset.univ) (fun s _ => hF s) (fun s _ => hscatter s)).smul hsum q⁻¹
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    abs_of_nonneg (inv_pos.mpr hq).le, show (Fintype.card Signed : ℝ) = q from rfl,
    inv_mul_cancel_left₀ hq.ne'] at ht
  exact ht

/-- The full original loop has a normalized marginal at any native joint coordinate. -/
theorem loop_marginal (H : R.Bounds clip width C Λ) (hs : PaintSupply G N Z)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    {d : ℕ} (hd : d + 1 ≤ N) (j : Fin (d + 1)) (i0 : Joint B G) :
    (∑ q : Fin d → Joint B G,
      ‖(((d + 1).factorial : ℝ)⁻¹) •
        entry (fun z => loop R (fine G B z)) x (Fin.insertNth j i0 q)‖) ≤
      loopCost G N Z width Λ ratio.count *
        ((townCost G : ℝ) * countCost (weaker N (entryWidth N ratio.count width))) ^ d := by
  have hr := width_positive H.width N ratio.count
  have hw : 0 < weaker N (entryWidth N ratio.count width) := by unfold weaker; positivity
  have hcost : 0 ≤ loopCost G N Z width Λ ratio.count :=
    mul_nonneg (mul_nonneg (Extra.Iteration.Cost.nonneg H.two) (atomCost_nn hs H.width 2))
      (count_pos (half_pos hr)).le
  exact ScatterAnchoredSum.normalized (loop_beacons B H hs x hx).2 (town B) hw hcost hd j i0

end YM.Integration.NativeJointLoopTensor
end
