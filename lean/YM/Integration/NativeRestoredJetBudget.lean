import YM.Integration.QLocalGradedVacuumLayers
import YM.MatchingLedger.Mountain.Miner
import YM.Comparison.RG02.Assembly.Contact

/-! Full atom jet costs from the original exponential length receipt.
The native complex radius is exp(width/2)-1 >= width/2. After the explicit
Taylor factorial normalization, this leaves a finite polynomial in the
reciprocal width. Every atom coefficient, list occurrence and root stays
unchanged. These are normalized multilinear operator norms, not an assumed
coordinate-l1 polynomial norm equivalence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeRestoredJetBudget

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Comparison.RG02.Assembly MatchingLedger.Mountain
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} {s : Side} {k : ℕ}

def factor (G : Gauge) (cap d : ℕ) (width : ℝ) : ℝ :=
  (max 1 |Work.F02.slotConst G|) ^ cap *
    (1 + (2 : ℝ) ^ (d + 1) / width) ^ d * (1 + |Miner.amount G d|) ^ d

def jetNorm (a : Atom G k) (o : Site s) (d : ℕ) : ℝ :=
  ‖(d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d
    (fun A : fieldDir G s 1 => a.unmasked (represent A) o) 0‖

private theorem factor_nonnegative {width : ℝ} (hw : 0 < width) (cap d : ℕ) :
    0 ≤ factor G cap d width := by
  unfold factor
  positivity

private theorem native_factor {width : ℝ} (hw : 0 < width)
    (d cap : ℕ) (hk : k ≤ cap) :
    (d.factorial : ℝ)⁻¹ * Miner.value G d k width ≤ factor G cap d width := by
  have hr : width / 2 ≤ Work.F02.radius width := by
    have h := Real.add_one_le_exp (width / 2)
    unfold Work.F02.radius
    linarith
  have hrpos := Work.F02.radius_pos hw
  have hratio : (2 : ℝ) ^ d / Work.F02.radius width ≤ (2 : ℝ) ^ (d + 1) / width := by
    calc
      _ ≤ (2 : ℝ) ^ d / (width / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hw) hr
      _ = _ := by rw [div_div_eq_mul_div, pow_succ]
  have hpow : (1 + (2 : ℝ) ^ d / Work.F02.radius width) ^ d ≤
      (1 + (2 : ℝ) ^ (d + 1) / width) ^ d :=
    pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) hratio) d
  have hslot : |Work.F02.slotConst G| ^ k ≤ (max 1 |Work.F02.slotConst G|) ^ cap :=
    (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) k).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  have ha : |1 + Miner.amount G d| ≤ 1 + |Miner.amount G d| := by
    simpa only [abs_one] using abs_add_le (1 : ℝ) (Miner.amount G d)
  have hlast : (1 + Miner.amount G d) ^ d ≤ (1 + |Miner.amount G d|) ^ d :=
    (le_abs_self _).trans ((abs_pow ..).trans_le
      (pow_le_pow_left₀ (abs_nonneg _) ha d))
  have hf : (d.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have he : (d.factorial : ℝ)⁻¹ * Miner.value G d k width =
      |Work.F02.slotConst G| ^ k *
        (1 + (2 : ℝ) ^ d / Work.F02.radius width) ^ d *
          (1 + Miner.amount G d) ^ d := by
    unfold Miner.value Miner.richness Push.Uniform.composeCost
    calc
      _ = ((d.factorial : ℝ)⁻¹ * (d.factorial : ℝ)) *
          (|Work.F02.slotConst G| ^ k *
            (1 + (2 : ℝ) ^ d / Work.F02.radius width) ^ d *
              (1 + Miner.amount G d) ^ d) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hf, one_mul]
  rw [he]
  unfold factor
  calc
    _ ≤ |Work.F02.slotConst G| ^ k *
        (1 + (2 : ℝ) ^ d / Work.F02.radius width) ^ d *
          (1 + |Miner.amount G d|) ^ d :=
      mul_le_mul_of_nonneg_left hlast (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul hslot hpow (by positivity) (by positivity)) (by positivity)

/-- The full normalized atom tensor, uniformly in the actual period and root. -/
theorem atom_jet_bound (a : Atom G k) (o : Site s) {width : ℝ}
    (hw : 0 < width) (d cap : ℕ) (hk : k ≤ cap) :
    jetNorm a o d ≤ a.budget width * factor G cap d width := by
  have hm := Miner.atoms (G := G) (n := s) 1 o hw d
    (x := (0 : fieldDir G s 1)) (by simp) a
  have hn : ‖iteratedFDeriv ℝ d
      (fun A : fieldDir G s 1 => a.unmasked (represent A) o) 0‖ ≤
        a.budget width * Miner.value G d k width := by
    simpa only [Miner.fortune, Lattice.pull_id] using hm.norm_le d le_rfl
  have hfi : (0 : ℝ) ≤ (d.factorial : ℝ)⁻¹ := by positivity
  have hb : 0 ≤ a.budget width := by unfold Atom.budget Atom.magnitude; positivity
  unfold jetNorm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hfi]
  calc
    _ ≤ (d.factorial : ℝ)⁻¹ * (a.budget width * Miner.value G d k width) :=
      mul_le_mul_of_nonneg_left hn hfi
    _ = a.budget width * ((d.factorial : ℝ)⁻¹ * Miner.value G d k width) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (native_factor hw d cap hk) hb

/-- Evaluation on a repeated field direction keeps its exact degree factor. -/
theorem atom_jet_value (a : Atom G k) (o : Site s) {width : ℝ}
    (hw : 0 < width) (d cap : ℕ) (hk : k ≤ cap) (A : fieldDir G s 1) :
    ‖jet (fun B : fieldDir G s 1 => a.unmasked (represent B) o) d A‖ ≤
      a.budget width * factor G cap d width * ‖A‖ ^ d := by
  let L := (d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d
    (fun B : fieldDir G s 1 => a.unmasked (represent B) o) 0
  have h : ‖L (fun _ => A)‖ ≤ jetNorm a o d * ‖A‖ ^ d := by
    simpa only [jetNorm, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      L.le_opNorm (fun _ => A)
  exact h.trans (mul_le_mul_of_nonneg_right (atom_jet_bound a o hw d cap hk) (by positivity))

private theorem paid_mono {f g : ℕ → ℝ} {C R : ℝ}
    (h : SumBudget f C) (hR : 0 ≤ R) (hg : ∀ i, 0 ≤ g i)
    (hle : ∀ i, g i ≤ f i * R) : SumBudget g (C * R) := by
  have ht := h.2.1.mul_right R
  have hs : Summable g := ht.of_nonneg_of_le hg hle
  refine ⟨hg, hs, (hs.tsum_le_tsum hle ht).trans ?_⟩
  rw [tsum_mul_right]
  exact mul_le_mul_of_nonneg_right h.2.2 hR

private theorem list_sum_le {ι : Type*} (l : List ι) (f g : ι → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  revert h
  induction l with
  | nil => intro _h; simp only [List.map_nil, List.sum_nil, le_refl]
  | cons a l ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h a (List.mem_cons_self ..))
        (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem list_sum_mul {ι : Type*} (l : List ι) (f : ι → ℝ) (R : ℝ) :
    (l.map fun a => f a * R).sum = (l.map f).sum * R := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, zero_mul]
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, add_mul]

variable {layers : List (Piece G s)} {p : BudgetPoint}
    {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)

private theorem original_budget (a : Piece G s) (ha : a ∈ layers) (o : Site s) :
    SumBudget (fun i : ℕ => if (a.packet.labels i).site = o then
      (H.packets.atom a i).budget width else 0) (H.packets.pieceCost a) := by
  simpa only [Atom.budget] using H.packets.exponential a ha o

/-- The absolute original atom coefficient mass is paid by its original piece cost. -/
theorem magnitude_budget (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers) (o : Site s) :
    SumBudget (fun i : ℕ => if (a.packet.labels i).site = o then
      (H.packets.atom a i).magnitude else 0) (H.packets.pieceCost a) := by
  have hn (i : ℕ) : 0 ≤ (if (a.packet.labels i).site = o then
      (H.packets.atom a i).magnitude else 0) := by
    split
    · unfold Atom.magnitude
      positivity
    · exact le_rfl
  have he (i : ℕ) : (if (a.packet.labels i).site = o then
      (H.packets.atom a i).magnitude else 0) ≤
        (if (a.packet.labels i).site = o then (H.packets.atom a i).budget width else 0) * 1 := by
    by_cases hi : (a.packet.labels i).site = o
    · simpa only [if_pos hi, mul_one] using (H.packets.atom a i).lower_budget width hw
    · simp only [if_neg hi, zero_mul, le_refl]
  simpa only [mul_one] using paid_mono (original_budget H a ha o) zero_le_one hn he

/-- Every full normalized tensor remains in the original root class. -/
theorem jet_budget (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers)
    (o : Site s) (d : ℕ) :
    SumBudget (fun i : ℕ => if (a.packet.labels i).site = o then
      jetNorm (H.packets.atom a i) (a.packet.labels i).site d else 0)
      (H.packets.pieceCost a * factor G rankCap d width) := by
  apply paid_mono (original_budget H a ha o) (factor_nonnegative hw rankCap d)
  · intro i
    split
    · exact norm_nonneg _
    · exact le_rfl
  · intro i
    by_cases hi : (a.packet.labels i).site = o
    · simpa only [if_pos hi] using atom_jet_bound (H.packets.atom a i)
        (a.packet.labels i).site hw d rankCap (H.packets.rank_bounded a ha)
    · simp only [if_neg hi, zero_mul, le_refl]

/-- Sum over the unchanged finite layer list, preserving duplicate and zero rows. -/
theorem total_magnitude (hw : 0 < width) (o : Site s) :
    (layers.map fun a => ∑' i : ℕ, if (a.packet.labels i).site = o then
      (H.packets.atom a i).magnitude else 0).sum ≤ budget := by
  exact (list_sum_le layers _ H.packets.pieceCost
    (fun a ha => (magnitude_budget H hw a ha o).2.2)).trans H.packets.total

/-- Same per-root total with the full nonlinear derivative factor displayed. -/
theorem total_jet (hw : 0 < width) (o : Site s) (d : ℕ) :
    (layers.map fun a => ∑' i : ℕ, if (a.packet.labels i).site = o then
      jetNorm (H.packets.atom a i) (a.packet.labels i).site d else 0).sum ≤
        budget * factor G rankCap d width := by
  refine (list_sum_le layers _ (fun a => H.packets.pieceCost a * factor G rankCap d width)
    (fun a ha => (jet_budget H hw a ha o d).2.2)).trans ?_
  rw [list_sum_mul]
  exact mul_le_mul_of_nonneg_right H.packets.total (factor_nonnegative hw rankCap d)

end YM.Integration.NativeRestoredJetBudget
end
