import YM.Integration.NativeRestoredJetBudget
import YM.Push.STATIONARY_UNIFORM.Support

/-! The original atom's ordered, factorial-normalized physical tensor.
Locality is proved from the literal transported-curvature walk. Half of the
original exponential width pays its full analytic jet; the remaining half
pays simultaneous spatial decay at every derivative coordinate. No field
Taylor truncation, translation invariance, or lattice-cardinality factor is
used. The cap on the decay rate will keep the later lattice-counting price
polynomial in reciprocal width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeAtomTensorLocality

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open Comparison.RG02.Assembly MatchingLedger.Mountain Push.Uniform
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {s : Side} {k : ℕ}

abbrev Index (G : Gauge) (s : Side) := Body 1 s × G.ColorIndex

def location (i : Index G s) : Site s := i.1.1

def coordinate (i : Index G s) : fieldDir G s 1 :=
  fun e => if e = i.1 then EuclideanSpace.single i.2 1 else 0

/-- Every individual real color coordinate has its original unit norm. -/
theorem coordinate_norm (i : Index G s) : ‖coordinate i‖ = 1 := by
  have hc : ‖(EuclideanSpace.single i.2 (1 : ℝ) : G.Color)‖ = 1 := by simp
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)).2
    intro e
    by_cases he : e = i.1
    · simpa only [coordinate, if_pos he, hc] using (le_refl (1 : ℝ))
    · simp only [coordinate, if_neg he, norm_zero, zero_le_one]
  · simpa only [coordinate, ↓reduceIte, hc] using norm_le_pi_norm (coordinate i) i.1

private theorem coordinate_tint (i : Index G s) :
    tint G (Body 1 s) (bolt i) = coordinate i := by
  rcases i with ⟨b, c⟩
  ext e j
  by_cases he : e = b
  · subst e
    simp [tint, bolt, coordinate, Pi.single_apply]
  · simp [tint, bolt, coordinate, he]

/-- Coefficients are ordered tensors; repeated indices are retained. -/
def tensor (a : Atom G k) (o : Site s) (d : ℕ) (q : Fin d → Index G s) : ℝ :=
  (d.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ d
    (fun A : fieldDir G s 1 => a.unmasked (represent A) o) 0
      (fun j => coordinate (q j))

private theorem atom_smooth (a : Atom G k) (o : Site s) :
    ContDiffAt ℝ ω (fun A : fieldDir G s 1 => a.unmasked (represent A) o) 0 := by
  simpa only [Miner.fortune, Lattice.pull_id] using
    (Miner.atoms (G := G) (n := s) 1 o (by norm_num : (0 : ℝ) < 1) 0
      (x := (0 : fieldDir G s 1)) (by simp) a).analytic

/-- This is exactly the native coefficient in the real physical coordinate chart. -/
theorem tensor_entry (a : Atom G k) (o : Site s) (d : ℕ) (q : Fin d → Index G s) :
    tensor a o d q = (d.factorial : ℝ)⁻¹ *
      entry (fun v : Positions (Index G s) =>
        a.unmasked (represent (tint G (Body 1 s) v)) o) 0 q := by
  let L := (tint G (Body 1 s)).toContinuousLinearMap
  have hs : ContDiffAt ℝ d
      (fun A : fieldDir G s 1 => a.unmasked (represent A) o) (L 0) := by
    simpa only [map_zero] using (atom_smooth a o).of_le le_top
  unfold entry
  rw [show (fun v : Positions (Index G s) =>
      a.unmasked (represent (tint G (Body 1 s) v)) o) =
      (fun A : fieldDir G s 1 => a.unmasked (represent A) o) ∘ L from rfl,
    contact_right L hs, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [tensor, L, ContinuousLinearEquiv.coe_coe, coordinate_tint]

/-- Every link actually read by the original atom is within twice its true length. -/
theorem atom_local (a : Atom G k) (o : Site s) (U V : Config G s)
    (h : ∀ e : Edge (Site s), separation o e.1 ≤ 2 * a.length → U e = V e) :
    a.unmasked U o = a.unmasked V o := by
  apply congrArg a.poly
  funext j
  rw [Work.F02.atSite_curvature, Work.F02.atSite_curvature]
  apply congrArg G.curvature
  apply path_same
  intro e he
  apply h e
  have hleg : (a.leg j).length ≤ a.length :=
    Finset.single_le_sum (fun i _ => Nat.zero_le ((a.leg i).length)) (Finset.mem_univ j)
  have hw : (Work.F02.slotWalk (a.leg j)).length ≤ 2 * (a.leg j).length := by
    simp only [Work.F02.slotWalk, List.length_append, Lattice.reverse,
      List.length_map, List.length_reverse]
    change (a.leg j).walk.length + 4 + (a.leg j).walk.length ≤
      2 * ((a.leg j).walk.length + 4)
    omega
  exact he.trans (hw.trans (Nat.mul_le_mul_left 2 hleg))

/-- A derivative coordinate outside the actual atom region annihilates the full tensor. -/
theorem tensor_zero (a : Atom G k) (o : Site s) (d : ℕ)
    (q : Fin d → Index G s) (j : Fin d)
    (hj : ¬ separation o (location (q j)) ≤ 2 * a.length) :
    tensor a o d q = 0 := by
  let P : fieldDir G s 1 →L[ℝ] fieldDir G s 1 :=
    ContinuousLinearMap.pi fun e => if separation o e.1 ≤ 2 * a.length
      then ContinuousLinearMap.proj e else 0
  let f : fieldDir G s 1 → ℝ := fun A => a.unmasked (represent A) o
  have heq : f = f ∘ P := by
    funext A
    apply atom_local
    intro e he
    rw [Work.F03.represent_link, Work.F03.represent_link]
    congr 1
    simp only [P, ContinuousLinearMap.pi_apply, if_pos he,
      ContinuousLinearMap.proj_apply]
  have hs : ContDiffAt ℝ d f (P 0) := by
    simpa only [map_zero] using (atom_smooth a o).of_le le_top
  have hd := congrArg (fun F : fieldDir G s 1 → ℝ => iteratedFDeriv ℝ d F 0) heq
  rw [contact_right P hs, map_zero] at hd
  have hz : P (coordinate (q j)) = 0 := by
    funext e
    by_cases he : separation o e.1 ≤ 2 * a.length
    · have hn : e ≠ (q j).1 := by
        intro h
        apply hj
        simpa only [h, location] using he
      simp only [P, ContinuousLinearMap.pi_apply, if_pos he,
        ContinuousLinearMap.proj_apply, coordinate, if_neg hn, Pi.zero_apply]
    · simp only [P, ContinuousLinearMap.pi_apply, if_neg he,
        zero_apply, Pi.zero_apply]
  unfold tensor
  change (d.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ d f 0 (fun i => coordinate (q i)) = 0
  rw [hd, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    (iteratedFDeriv ℝ d f 0).map_coord_zero j hz, mul_zero]

/-- The parent operator bound is applied only to literal unit coordinate vectors. -/
theorem tensor_bound (a : Atom G k) (o : Site s) {width : ℝ}
    (hw : 0 < width) (d cap : ℕ) (hk : k ≤ cap) (q : Fin d → Index G s) :
    ‖tensor a o d q‖ ≤ a.budget width * NativeRestoredJetBudget.factor G cap d width := by
  let L := (d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d
    (fun A : fieldDir G s 1 => a.unmasked (represent A) o) 0
  have h : ‖tensor a o d q‖ ≤ NativeRestoredJetBudget.jetNorm a o d := by
    simpa only [L, tensor, NativeRestoredJetBudget.jetNorm, coordinate_norm,
      Finset.prod_const_one, mul_one, smul_apply,
      smul_eq_mul] using L.le_opNorm (fun j => coordinate (q j))
  exact h.trans (NativeRestoredJetBudget.atom_jet_bound a o hw d cap hk)

def rate (d : ℕ) (width : ℝ) : ℝ := min (width / (4 * ((d : ℝ) + 1))) 1

/-- A simultaneous decay factor for every original tensor coordinate. -/
theorem tensor_decay (a : Atom G k) (o : Site s) {width : ℝ}
    (hw : 0 < width) (d cap : ℕ) (hk : k ≤ cap) (q : Fin d → Index G s) :
    ‖tensor a o d q‖ ≤
      a.budget width * NativeRestoredJetBudget.factor G cap d (width / 2) *
        Real.exp (-rate d width * spanSites location o q) := by
  have hr : 0 ≤ rate d width := by unfold rate; positivity
  have hf : 0 ≤ NativeRestoredJetBudget.factor G cap d (width / 2) := by
    unfold NativeRestoredJetBudget.factor
    positivity
  by_cases hnear : ∀ j, separation o (location (q j)) ≤ 2 * a.length
  · have hsum : spanSites location o q ≤ d * (2 * a.length) := by
      exact (Finset.sum_le_sum (fun j _ => hnear j)).trans_eq (by simp)
    have hm : rate d width * (4 * ((d : ℝ) + 1)) ≤ width :=
      (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
    have hrate : rate d width * (2 * (d : ℝ)) ≤ width / 2 := by nlinarith
    have hsumR : (spanSites location o q : ℝ) ≤ (d : ℝ) * (2 * (a.length : ℝ)) := by
      exact_mod_cast hsum
    have hpaid : rate d width * spanSites location o q ≤ width / 2 * a.length := by
      calc
        _ ≤ rate d width * ((d : ℝ) * (2 * (a.length : ℝ))) :=
          mul_le_mul_of_nonneg_left hsumR hr
        _ = (rate d width * (2 * (d : ℝ))) * a.length := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hrate (by positivity)
    have hb : a.budget (width / 2) ≤
        a.budget width * Real.exp (-rate d width * spanSites location o q) := by
      unfold Atom.budget
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
      unfold Atom.magnitude
      positivity
    calc
      _ ≤ a.budget (width / 2) * NativeRestoredJetBudget.factor G cap d (width / 2) :=
        tensor_bound a o (half_pos hw) d cap hk q
      _ ≤ (a.budget width * Real.exp (-rate d width * spanSites location o q)) *
          NativeRestoredJetBudget.factor G cap d (width / 2) :=
        mul_le_mul_of_nonneg_right hb hf
      _ = _ := by ring
  · push Not at hnear
    obtain ⟨j, hj⟩ := hnear
    rw [tensor_zero a o d q j (not_le.mpr hj), norm_zero]
    have hb : 0 ≤ a.budget width := by unfold Atom.budget Atom.magnitude; positivity
    positivity

end YM.Integration.NativeAtomTensorLocality
end
