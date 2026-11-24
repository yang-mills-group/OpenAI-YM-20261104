import YM.Integration.RootedJointSignedInitialization
import YM.RG3.Annuncia.Revenue

/-!
Assemble the native origin-aggregation receipts into an actual `Served`
transport.  The input is already a represented polynomial on the compatible
`Replica` census.  This does not turn an arbitrary unmasked caption bank into
a `Carton`, and does not construct the preceding product-regrouping or census
restriction.  The same representation, unmarked K, forced partners and
support headers occur on both sides.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeReplicaServed
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent RG3.Annuncia
open JointSignedInitialization
open scoped BigOperators Classical

variable {V W : Type} [DecidableEq V] [Fintype W] [DecidableEq W]
    (u : W → V) (B : Census V) (γ : W → ℂ)

/-- `Replica` admits at most one origin per output slot, so aggregation
preserves the exclusion of degrees zero and one. -/
theorem mouth_rises {P : Poly (Replica u B)} (h : rises P) :
    rises (Replica.mouth u B γ P) := by
  intro i hi
  by_contra hn
  apply hi
  rw [Replica.quota]
  apply Finset.sum_eq_zero
  intro j _
  by_cases he : Replica.bill u B j = i
  · rw [if_pos he]
    have hp : P.part j = 0 := by
      by_contra hp
      apply hn
      have hj := h j hp
      rw [← he, Replica.length]
      exact hj
    rw [hp, mul_zero]
  · rw [if_neg he]

variable {G : Gauge} {n : Side}

/-- Both regular and forced pieces retain their original masking and
flag-equality conditions, with the original support sets. -/
theorem mouth_carton (o : V → Site n)
    {H : Support n → Config G n → Poly (Replica u B)}
    {K : Box n → Config G n → Poly (Replica u B)} {t : ℝ}
    (h : Carton (o ∘ u) H K t) :
    Carton o (fun s U => Replica.mouth u B γ (H s U))
      (fun s U => Replica.mouth u B γ (K s U)) t := by
  constructor
  · intro s
    exact ⟨Replica.gem u B γ o (h.exp s).1,
      fun U => mouth_rises u B γ ((h.exp s).2 U)⟩
  · intro s
    exact ⟨Replica.cash u B γ o (h.flag s).1,
      fun U => mouth_rises u B γ ((h.flag s).2 U)⟩

/-- The cost is unchanged and independent of the number of origins.
The coefficient envelope comes from native `Replica.save`. -/
theorem mouth_towed {A Y : Type} (w : V → ℝ) (a : W → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    (hγ : ∀ i, ‖γ i‖ ≤ a i) {X : A → Support n}
    {F : A → Y → Poly (Replica u B)} {b : ℕ} {e c : ℝ}
    (h : Towed (fun i => a i * w (u i)) X F b e c) :
    Towed w X (fun i U => Replica.mouth u B γ (F i U)) b e c := by
  obtain ⟨p, hp, hHit, hCoeff⟩ := Replica.save u B w a hw
    (fun _ : Unit => γ) (fun _ => hγ) ha h
  refine ⟨fun i => RG3.Riding.unitPrice B w (p i), hp, hHit, fun i => ?_⟩
  exact ⟨p i, (hCoeff i).1, fun U j => (hCoeff i).2 () U j, le_rfl⟩

variable [Fintype V]

/-- Exact reconstruction after native aggregation, including all original
unmarked gas factors and the complete forced polynomial. -/
theorem mouth_restore (P : Rep G n)
    (Φ : W → Config G n → ℂ) (ω : W → Box n → Config G n → ℂ)
    (H : Support n → Config G n → Poly (Replica u B))
    (K : Box n → Config G n → Poly (Replica u B))
    (hH : ∀ s U, (H s U).part (Replica u B).quiet = 0) :
    (fun U => Replica.mouth u B γ (restore P Φ ω H K U)) =
      restore P (Rooted.aggregate u γ Φ)
        (fun v s U => Rooted.aggregate u γ (fun i => ω i s) v U)
        (fun s U => Replica.mouth u B γ (H s U))
        (fun s U => Replica.mouth u B γ (K s U)) := by
  funext U
  have hz : (Mach (Replica u B) (fun i => Φ i U) + ∑ s, H s U).part
      (Replica u B).quiet = 0 := by
    simp only [Poly.part_plus, mute, Poly.part_sum, hH, Finset.sum_const_zero, add_zero]
  have hb (s : Box n) :
      Replica.mouth u B γ (bar P.activities (Replica u B) U s) =
        bar P.activities B U s := by
    exact Replica.single u B γ _
  unfold restore
  rw [Replica.csmul, map_mul, Replica.passed u B γ _ hz]
  simp only [map_add, map_sum, Rooted.mouth_mach]
  rw [Replica.estate]
  simp only [Function.comp_def, map_add, hb, Rooted.mouth_mach]
  rfl

/-- A genuine compatible-census `Served` receipt supplies the aggregated
one on the very same representation.  The hypothesis is not a placeholder
for admitting an arbitrary `KP`: its regular and forced conditions are used. -/
theorem mouth_served (P : Rep G n)
    (Φ : W → Config G n → ℂ) (ω : W → Box n → Config G n → ℂ)
    (Z : Config G n → Poly (Replica u B)) (o : V → Site n)
    (w : V → ℝ) (a : W → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hγ : ∀ i, ‖γ i‖ ≤ a i) {e c : ℝ}
    (h : Served P Φ ω Z (o ∘ u) (fun i => a i * w (u i)) e c) :
    Served P (Rooted.aggregate u γ Φ)
      (fun v s U => Rooted.aggregate u γ (fun i => ω i s) v U)
      (fun U => Replica.mouth u B γ (Z U)) o w e c := by
  obtain ⟨H, K, hCarton, hRegular, hForced, rfl⟩ := h
  refine ⟨fun s U => Replica.mouth u B γ (H s U),
    fun s U => Replica.mouth u B γ (K s U),
    mouth_carton u B γ o hCarton,
    mouth_towed u B γ w a hw ha hγ hRegular,
    mouth_towed u B γ w a hw ha hγ hForced, ?_⟩
  exact mouth_restore u B γ P Φ ω H K (fun s U => (hCarton.exp s).1.sil U)

end YM.Integration.NativeReplicaServed
