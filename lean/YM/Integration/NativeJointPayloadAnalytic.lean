import YM.Integration.NativeJointPayloadTensor
import YM.Push.STATIONARY_UNIFORM.ScoreBounds

/-! Analyticity of the full original varying-root payload on the actual joint
chart. A finite root decomposition is used only qualitatively. Its auxiliary
zeroed coefficients do not change any original atom, row, credit or budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeJointPayloadAnalytic

open Function Filter Set Metric Lattice Wilson RG Precision Tree Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Push.Uniform
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {c f : Side} {ratio : Ratio c f} (B : Forest ratio)
variable {N : ℕ} {Z width budget : ℝ}
variable {layers : List (Piece G f)} {p : BudgetPoint} {order rankCap : ℕ}
variable (H : GradedVacuumLayers layers p order rankCap width budget)

private def rootAtom (a : Piece G f) (o : Site f) (i : ℕ) : Atom G a.rank :=
  if (a.packet.labels i).site = o then H.packets.atom a i
  else { H.packets.atom a i with coeff := fun _ => 0 }

private theorem rootAtom_budget (a : Piece G f) (o : Site f) (i : ℕ) :
    (rootAtom H a o i).budget width =
      if (a.packet.labels i).site = o then (H.packets.atom a i).budget width else 0 := by
  by_cases hi : (a.packet.labels i).site = o
  · simp only [rootAtom, if_pos hi]
  · simp only [rootAtom, if_neg hi, Atom.budget, Atom.magnitude,
      abs_zero, Finset.sum_const_zero, zero_mul]

private theorem rootAtom_action (a : Piece G f) (o : Site f) (i : ℕ)
    (U : Config G f) :
    (rootAtom H a o i).unmasked U o =
      if (a.packet.labels i).site = o then
        (H.packets.atom a i).unmasked U (a.packet.labels i).site else 0 := by
  by_cases hi : (a.packet.labels i).site = o
  · simp only [rootAtom, if_pos hi]
    exact congrArg (fun q => (H.packets.atom a i).unmasked U q) hi.symm
  · simp only [rootAtom, if_neg hi, Atom.unmasked, Atom.poly,
      zero_mul, Finset.sum_const_zero]

private theorem root_budget (a : Piece G f) (ha : a ∈ layers) (o : Site f) :
    SumBudget (fun i => (rootAtom H a o i).budget width) (H.packets.pieceCost a) := by
  simp_rw [rootAtom_budget]
  simpa only [Atom.budget] using H.packets.exponential a ha o

private theorem root_summable (hw : 0 < width) (a : Piece G f) (ha : a ∈ layers)
    (o : Site f) (U : Config G f) :
    Summable (fun i : ℕ => (rootAtom H a o i).unmasked U o) := by
  apply Summable.of_norm_bounded ((root_budget H a ha o).2.1.mul_right ((2 : ℝ)^a.rank))
  intro i
  calc
    _ ≤ (rootAtom H a o i).magnitude * 2^a.rank := by
      simpa only [Real.norm_eq_abs] using (rootAtom H a o i).unmasked_bound U o
    _ ≤ (rootAtom H a o i).budget width * 2^a.rank :=
      mul_le_mul_of_nonneg_right ((rootAtom H a o i).lower_budget width hw) (by positivity)

private theorem root_sum (hw : 0 < width) (a : Piece G f) (ha : a ∈ layers)
    (U : Config G f) :
    unmaskedPayload a.packet U =
      ∑ o : Site f, ∑' i : ℕ, (rootAtom H a o i).unmasked U o := by
  calc
    _ = ∑' i : ℕ, (H.packets.atom a i).unmasked U (a.packet.labels i).site :=
      tsum_congr fun i => H.packets.original_action a ha i U
    _ = ∑' i : ℕ, ∑ o : Site f, (rootAtom H a o i).unmasked U o := by
      apply tsum_congr
      intro i
      simp_rw [rootAtom_action]
      simp
    _ = _ := Summable.tsum_finsetSum (fun o _ => root_summable H hw a ha o U)

include H in
/-- Native analyticity for the full original payload, retaining every root. -/
theorem payload_analytic (hs : PaintSupply G N Z) (hw : 0 < width)
    (x : Positions (Joint B G)) (hx : x ∈ ball 0 1)
    (a : Piece G f) (ha : a ∈ layers) :
    ContDiffAt ℝ ω (fun z => unmaskedPayload a.packet (fine G B z)) x := by
  let F (o : Site f) (z : Positions (Joint B G)) :=
    ∑' i : ℕ, (rootAtom H a o i).unmasked (fine G B z) o
  have hf (o : Site f) : ContDiffAt ℝ ω (F o) x := by
    have h := label_analytic B (rootAtom H a o) hw (root_budget H a ha o)
      (1 : Signed) hs o x hx
    simpa only [signedFine, Lattice.pull_id] using h
  have he : (fun z => unmaskedPayload a.packet (fine G B z)) =
      (fun z => ∑ o : Site f, F o z) := by
    funext z
    exact root_sum H hw a ha (fine G B z)
  rw [he]
  exact ContDiffAt.sum (s := Finset.univ) (fun o _ => hf o)

include H in
/-- The exact zero-field inlet used by the mixed normalized-jet calculation. -/
theorem payload_analytic_zero (hs : PaintSupply G N Z) (hw : 0 < width)
    (a : Piece G f) (ha : a ∈ layers) :
    ContDiffAt ℝ ω (fun z => unmaskedPayload a.packet (fine G B z)) 0 :=
  payload_analytic B H hs hw 0 (by simp) a ha

end YM.Integration.NativeJointPayloadAnalytic
end
