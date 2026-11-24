import YM.Integration.ActualGradedVacuum
import YM.Integration.ActualNormalizedRayJets

/-! Exact full nonlinear jets of the original restored vacuum list.
A row has only a leading rank, not a homogeneous full field action. Thus
all higher payload jets survive: the coupling exponent shifts the field
jet, and rows disappear only below their original leading joint degree.
Every original list occurrence and every countable atom row is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeRestoredLayerJets

open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open Comparison.RG02 Comparison.RG02.Assembly MatchingLedger.Mountain
open scoped Topology BigOperators ContDiff Classical

section ScalarShift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Full joint jet of a scalar coupling power times an analytic field function. -/
theorem power_jet (f : E → ℝ) (hf : ContDiffAt ℝ ω f 0)
    (e n : ℕ) (g : ℝ) (A : E) :
    jet (fun z : ℝ × E => z.1 ^ e * f z.2) n (g, A) =
      if e ≤ n then g ^ e * jet f (n - e) A else 0 := by
  let F : ℝ × E → ℝ := fun z => z.1 ^ e * f z.2
  have hF : GradeAt e F := by
    have hpow := GradeAt.shifts (fun z : ℝ × E => z.1) contDiffAt_fst rfl e
    have hfield := GradeAt.unchecked (hf.comp (0 : ℝ × E) contDiffAt_snd)
    simpa only [F, Function.comp_def, smul_eq_mul, Nat.add_zero] using hpow.scale hfield
  by_cases hen : e ≤ n
  · rw [if_pos hen]
    let L : ℝ →L[ℝ] ℝ × E := ContinuousLinearMap.toSpanSingleton ℝ (g, A)
    let LA : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ A
    let R : ℝ →L[ℝ] ℝ := g ^ e • ContinuousLinearMap.id ℝ ℝ
    let q : ℝ → ℝ := fun t => g ^ e * f (t • A)
    have hf0 : ContDiffAt ℝ ω f (LA 0) := LA.map_zero.symm ▸ hf
    have hcomp : ContDiffAt ℝ ω (f ∘ LA) 0 := hf0.comp 0 LA.contDiff.contDiffAt
    have hq : ContDiffAt ℝ ω q 0 := by
      change ContDiffAt ℝ ω (R ∘ (f ∘ LA)) 0
      exact R.contDiff.contDiffAt.comp 0 hcomp
    have hv : ∀ᶠ t : ℝ in 𝓝[≠] 0,
        q t = (t ^ e)⁻¹ • (F ∘ L) t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := by simpa using ht
      change g ^ e * f (t • A) = (t ^ e)⁻¹ * ((t * g) ^ e * f (t • A))
      symm
      calc
        _ = ((t ^ e)⁻¹ * t ^ e) * (g ^ e * f (t • A)) := by rw [mul_pow]; ring
        _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero e ht0), one_mul]
    have h := ActualNormalizedRayJets.divided_coefficient
      (hF.coarse L.contDiff.contDiffAt L.map_zero) hq.continuousAt hv (n - e)
    have horder : e + (n - e) = n := by omega
    rw [horder] at h
    have hr : jet (F ∘ L) n 1 = jet F n (g, A) := by
      simpa [L] using jet_continuous_right L (hF.smooth.of_le le_top) (1 : ℝ)
    have hl : jet q (n - e) 1 = g ^ e * jet f (n - e) A := by
      change jet (R ∘ (f ∘ LA)) (n - e) 1 = _
      rw [← jet_apply_left R (f ∘ LA) (n - e) (hcomp.of_le le_top) (1 : ℝ),
        jet_continuous_right LA (hf.of_le le_top) (1 : ℝ)]
      simp [R, LA]
    rw [hl, hr] at h
    exact h.symm
  · rw [if_neg hen]
    exact hF.jet_z (g, A) (Nat.lt_of_not_ge hen)

private theorem list_smooth {ι : Type*} (l : List ι) (f : ι → E → ℝ)
    (h : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0) :
    ContDiffAt ℝ ω (fun z => (l.map fun a => f a z).sum) 0 := by
  revert h
  induction l with
  | nil =>
      intro _h
      simp only [List.map_nil, List.sum_nil]
      exact contDiffAt_const
  | cons a l ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact (h a (List.mem_cons_self ..)).add (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

private theorem list_jet {ι : Type*} (l : List ι) (f : ι → E → ℝ)
    (h : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0) (n : ℕ) (A : E) :
    jet (fun z => (l.map fun a => f a z).sum) n A =
      (l.map fun a => jet (f a) n A).sum := by
  revert h
  induction l with
  | nil =>
      intro _h
      simpa only [List.map_nil, List.sum_nil] using
        (GradeAt.grade_zero (n + 1) : GradeAt (n + 1) (fun _ : E => (0 : ℝ))).jet_z
          A (by omega : n < n + 1)
  | cons a l ih =>
      intro h
      have hl : ∀ b ∈ l, ContDiffAt ℝ ω (f b) 0 :=
        fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [List.map_cons, List.sum_cons]
      rw [show (fun z => f a z + (l.map fun b => f b z).sum) =
        f a + (fun z => (l.map fun b => f b z).sum) from rfl]
      unfold jet
      rw [iteratedFDeriv_add_apply ((h a (List.mem_cons_self ..)).of_le le_top)
        ((list_smooth l f hl).of_le le_top), _root_.add_apply, smul_add]
      exact congrArg (fun y => jet (f a) n A + y) (ih hl)
end ScalarShift

variable {G : Gauge} {s : Side} {layers : List (Piece G s)} {p : BudgetPoint}
    {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers layers p order rankCap width budget)

private theorem atom_budget (a : Piece G s) (ha : a ∈ layers) :
    Summable (fun i : ℕ => (H.packets.atom a i).budget width) := by
  let f (o : Site s) (i : ℕ) :=
    if (a.packet.labels i).site = o then (H.packets.atom a i).budget width else 0
  have hs (o : Site s) : Summable (f o) := by
    simpa only [f, Atom.budget] using (H.packets.exponential a ha o).2.1
  have ht := summable_sum (s := Finset.univ) (fun o _ => hs o)
  convert ht using 1
  funext i
  simp [f]

/-- The full field jet is the convergent sum of the same original atom jets. -/
theorem payload_jet (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers)
    (n : ℕ) (A : fieldDir G s 1) :
    jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B)) n A =
      ∑' i : ℕ, jet (fun B : fieldDir G s 1 =>
        (H.packets.atom a i).unmasked (represent B) (a.packet.labels i).site) n A := by
  let f (i : ℕ) (B : fieldDir G s 1) :=
    (H.packets.atom a i).unmasked (represent B) (a.packet.labels i).site
  let C (i : ℕ) := (H.packets.atom a i).budget width * Miner.value G n a.rank width
  have hC : Summable C := (atom_budget H a ha).mul_right _
  have hu (i : ℕ) (B : fieldDir G s 1) (hB : B ∈ ball 0 1) :
      Push.Uniform.Allows n (f i) B (C i) := by
    simpa only [f, C, Miner.fortune, Lattice.pull_id] using
      (Miner.atoms (G := G) (n := s) 1 (a.packet.labels i).site hw n hB (H.packets.atom a i))
  have hD : Summable (fun i => iteratedFDeriv ℝ n (f i) 0) :=
    .of_norm_bounded hC (fun i => (hu i 0 (by simp)).norm_le n le_rfl)
  have he : (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B)) =
      fun B => ∑' i : ℕ, f i B := by
    funext B
    exact tsum_congr fun i => H.packets.original_action a ha i (represent B)
  rw [he]
  unfold jet
  rw [Push.Uniform.iterated_at_sum isOpen_ball
      (convex_ball (0 : fieldDir G s 1) 1).isPreconnected hC hu
      (by simp : (0 : fieldDir G s 1) ∈ ball 0 1) n le_rfl,
    ContinuousMultilinearMap.tsum_eval hD]
  exact (tsum_const_smul'' ((n.factorial : ℝ)⁻¹)).symm

include H in
/-- Every finite list occurrence survives, with its full shifted field jet. -/
theorem restored_jet (hw : 0 < width) (n : ℕ) (g : ℝ) (A : fieldDir G s 1) :
    jet (Bulk.projected (ActualGradedVacuum.restored layers)) n (g, A) =
      (layers.map fun a => if a.power + 2 - a.rank ≤ n then
        g ^ (a.power + 2 - a.rank) *
          jet (fun B : fieldDir G s 1 => unmaskedPayload a.packet (represent B))
            (n - (a.power + 2 - a.rank)) A else 0).sum := by
  let f (a : Piece G s) (z : ℝ × fieldDir G s 1) :=
    z.1 ^ (a.power + 2 - a.rank) * unmaskedPayload a.packet (represent z.2)
  have hf (a : Piece G s) (ha : a ∈ layers) : ContDiffAt ℝ ω (f a) 0 :=
    (contDiffAt_fst.pow _).mul
      ((ActualGradedVacuum.payload_grade H hw a ha).smooth.comp
        (0 : ℝ × fieldDir G s 1) contDiffAt_snd)
  change jet (fun z => (layers.map fun a => f a z).sum) n (g, A) = _
  rw [list_jet layers f hf n (g, A)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact power_jet _ (ActualGradedVacuum.payload_grade H hw a ha).smooth _ n g A

/-- The same dictionary down to all original countable atom rows. -/
theorem restored_atom_jet (hw : 0 < width) (n : ℕ) (g : ℝ) (A : fieldDir G s 1) :
    jet (Bulk.projected (ActualGradedVacuum.restored layers)) n (g, A) =
      (layers.map fun a => if a.power + 2 - a.rank ≤ n then
        g ^ (a.power + 2 - a.rank) *
          ∑' i : ℕ, jet (fun B : fieldDir G s 1 =>
            (H.packets.atom a i).unmasked (represent B) (a.packet.labels i).site)
            (n - (a.power + 2 - a.rank)) A else 0).sum := by
  rw [restored_jet H hw]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  by_cases h : a.power + 2 - a.rank ≤ n
  · simp only [if_pos h, payload_jet H hw a ha]
  · simp only [if_neg h]

include H in
/-- Leading grade removes only lower degrees; it does not remove higher jets. -/
theorem row_below_leading (hw : 0 < width) (a : Piece G s) (ha : a ∈ layers)
    (n : ℕ) (hn : n < a.power + 2) (g : ℝ) (A : fieldDir G s 1) :
    jet (fun z : ℝ × fieldDir G s 1 => z.1 ^ (a.power + 2 - a.rank) *
      unmaskedPayload a.packet (represent z.2)) n (g, A) = 0 := by
  have hp := GradeAt.shifts
    (fun z : ℝ × fieldDir G s 1 => z.1) contDiffAt_fst rfl (a.power + 2 - a.rank)
  have hq := (ActualGradedVacuum.payload_grade H hw a ha).coarse
    (g := fun z : ℝ × fieldDir G s 1 => z.2) contDiffAt_snd rfl
  have he : (a.power + 2 - a.rank) + a.rank = a.power + 2 :=
    Nat.sub_add_cancel (H.leading_rank a ha)
  have hrow : GradeAt (a.power + 2) (fun z : ℝ × fieldDir G s 1 =>
      z.1 ^ (a.power + 2 - a.rank) * unmaskedPayload a.packet (represent z.2)) := by
    simpa only [he, Function.comp_def, smul_eq_mul] using hp.scale hq
  exact hrow.jet_z (g, A) hn

end YM.Integration.NativeRestoredLayerJets
end
