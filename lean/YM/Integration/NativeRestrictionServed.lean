import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.MergeProof.Bungalow
import YM.MergeProof.South.Window
import YM.Overlay.Terminal

/-! Exact deletion of names or addition of marker exclusions on one fixed
representation. The same regular/forced support headers and original gas
are retained. Restriction only removes coefficients, so nonnegative marker
weights pay no additional cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeRestrictionServed
open Function Finset MeasureTheory Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Trajectories Push.GridApprox.Nil
open scoped BigOperators Classical

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {B : Census V} {D : Census W} (u : Names B D)

omit [Fintype V] [Fintype W] in
private theorem share_card (i : B.Mode) : (u.share i).val.card = i.val.card := by
  change (i.val.image u.e).card = i.val.card
  exact Finset.card_image_iff.mpr u.e.injective.injOn

omit [Fintype V] [Fintype W] in
theorem restriction_rises {P : Poly D} (h : rises P) : rises (u.restriction P) := by
  intro i hi
  have he := h (u.share i) hi
  rwa [share_card] at he

omit [Fintype V] [Fintype W] in
private theorem restriction_send (i : B.Mode) (z : ℂ) :
    u.restriction (Poly.send (u.share i) z) = Poly.send i z := by
  apply Marker.Poly.ext
  intro j
  change (Poly.send (u.share i) z).part (u.share j) = (Poly.send i z).part j
  simp only [Poly.part_send, u.inj.eq_iff]

theorem restriction_mach (f : W → ℂ) :
    u.restriction (Mach D f) = Mach B (f ∘ u.e) := by
  apply Marker.Poly.ext
  intro i
  change (Mach D f).part (u.share i) = (Mach B (f ∘ u.e)).part i
  by_cases h0 : i.val.card = 0
  · have hi : i = B.quiet := Subtype.ext (Finset.card_eq_zero.mp h0)
    subst i
    rw [u.quiet, mute, mute]
  by_cases h1 : i.val.card = 1
  · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    have hi : i = B.fire v := Subtype.ext hv
    subst i
    rw [u.fire, sing, sing]
    rfl
  have hi : 2 ≤ i.val.card := by omega
  rw [hush f (u.share i) (by rw [share_card]; exact hi), hush (f ∘ u.e) i hi]

variable {G : Gauge} {n : Side}

/-- The original physical density is retained under marker restriction. -/
theorem restriction_birth (P : Rep G n) (F : W → Config G n → ℂ) :
    (fun U => u.restriction (Accent.birth D P F U)) =
      Accent.birth B P (F ∘ u.e) := by
  funext U
  unfold Accent.birth
  rw [u.smul, u.pass_restrict (mute D _), restriction_mach]
  rfl

private def restrictionLinear : Poly D →ₗ[ℂ] Poly B where
  toFun := u.restriction
  map_add' := map_add _
  map_smul' c P := u.smul P c

omit [Fintype V] [Fintype W] in
/-- Restrict once before the actual push or after any number of steps.
The same history, cutoff, period and complete numerator occur on both sides. -/
theorem restriction_gust (A : History G) (N p j : ℕ)
    (X : Config G (A.S.side j p) → Poly D) (hX : Integrable X (prior G _))
    {m : ℕ} (hm : m ≤ j) :
    gust A N p j (fun U => u.restriction (X U)) m hm =
      fun U => u.restriction (gust A N p j X m hm U) := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ l hl ih =>
    rw [gust_step A N p j _ hl, ih]
    funext U
    rw [gust_step A N p j _ hl]
    unfold StepData.push
    let L := (LinearMap.toContinuousLinearMap (restrictionLinear u)).restrictScalars ℝ
    have he := L.integral_comp_comm
      (StepData.push_slice (A.levels.transition_mass l p (A.β N p (l + 1))) U _
        (gust_live A N p j X hX hl))
    simp_rw [L.map_smul] at he
    exact he

omit [Fintype V] [Fintype W] in
theorem restriction_borne (o : W → Site n) {s : Support n}
    {F : Config G n → Poly D} {t : ℝ} (h : Borne o s F t) :
    Borne (o ∘ u.e) s (fun U => u.restriction (F U)) t := by
  refine ⟨fun U V h1 h2 => congrArg u.restriction (h.home U V h1 h2),
    fun q U => congrArg u.restriction (h.turns q U), fun i => h.me (u.share i), ?_⟩
  intro U i hi
  change (F U).part (u.share i) = 0
  apply h.scope U (u.share i)
  intro hs
  apply hi
  intro v hv
  exact hs (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

omit [Fintype V] [Fintype W] in
theorem restriction_burns (o : W → Site n) {s : Support n}
    {F : Config G n → Poly D} {t : ℝ} (h : Burns o s F t) :
    Burns (o ∘ u.e) s (fun U => u.restriction (F U)) t := by
  refine ⟨restriction_borne u o h.toBorne, ?_, ?_⟩
  · intro U hn
    apply h.permits U
    intro hz
    apply hn
    rw [hz, map_zero]
  · intro U
    change (F U).part (u.share B.quiet) = 0
    rw [u.quiet]
    exact h.sil U

omit [Fintype V] [Fintype W] in
theorem restriction_flow (o : W → Site n) {s : Box n}
    {F : Config G n → Poly D} {t : ℝ} (h : Flow o s F t) :
    Flow (o ∘ u.e) s (fun U => u.restriction (F U)) t := by
  refine ⟨restriction_borne u o h.toBorne, ?_⟩
  intro U hn
  apply h.permits U
  intro hz
  apply hn
  rw [hz, map_zero]

omit [Fintype V] [Fintype W] in
theorem restriction_carton (o : W → Site n)
    {H : Support n → Config G n → Poly D}
    {K : Box n → Config G n → Poly D} {t : ℝ} (h : Carton o H K t) :
    Carton (o ∘ u.e) (fun s U => u.restriction (H s U))
      (fun s U => u.restriction (K s U)) t := by
  constructor
  · intro s
    exact ⟨restriction_burns u o (h.exp s).1,
      fun U => restriction_rises u ((h.exp s).2 U)⟩
  · intro s
    exact ⟨restriction_flow u o (h.flag s).1,
      fun U => restriction_rises u ((h.flag s).2 U)⟩

omit [Fintype V] [Fintype W] in
private theorem restriction_toll (w : W → ℝ) (i : B.Mode) :
    Poly.toll (w ∘ u.e) i = Poly.toll w (u.share i) := by
  unfold Poly.toll Names.share
  rw [Finset.prod_image u.e.injective.injOn]
  rfl

omit [Fintype V] [Fintype W] in
theorem restriction_price (w : W → ℝ) (hw : ∀ i, 0 ≤ w i)
    (v : Sheet D) (hv : 0 ≤ v) :
    wordsPrice (w ∘ u.e) (v ∘ u.share) ≤ wordsPrice w v := by
  have he : wordsPrice (w ∘ u.e) (v ∘ u.share) =
      ∑ i ∈ Finset.univ.image u.share, Poly.toll w i * v i := by
    unfold wordsPrice
    rw [Finset.sum_image u.inj.injOn]
    apply Finset.sum_congr rfl
    intro i _
    rw [restriction_toll]
    rfl
  rw [he]
  unfold wordsPrice
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i _ _
  exact mul_nonneg (Finset.prod_nonneg fun j _ => hw j) (hv i)

omit [Fintype V] [Fintype W] in
theorem restriction_towed {A Y : Type} (w : W → ℝ) (hw : ∀ i, 0 ≤ w i)
    {S : A → Support n} {F : A → Y → Poly D} {b : ℕ} {e c : ℝ}
    (h : Towed w S F b e c) :
    Towed (w ∘ u.e) S (fun i U => u.restriction (F i U)) b e c := by
  obtain ⟨a, ha, hHit, hLoci⟩ := h
  refine ⟨a, ha, hHit, fun i => ?_⟩
  obtain ⟨v, hv, hBound, hPrice⟩ := hLoci i
  exact ⟨v ∘ u.share, fun j => hv (u.share j),
    fun U j => hBound U (u.share j), (restriction_price u w hw v hv).trans hPrice⟩

omit [Fintype V] [Fintype W] in
private theorem restriction_field (f : Box n → Poly D) (s : Support n) :
    u.restriction (field f s) = field (fun i => u.restriction (f i)) s := by
  unfold field
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  unfold grid
  split_ifs
  · exact map_prod ..
  · exact map_zero _

theorem restriction_restore (P : Rep G n)
    (Φ : W → Config G n → ℂ) (ω : W → Box n → Config G n → ℂ)
    (H : Support n → Config G n → Poly D) (K : Box n → Config G n → Poly D)
    (hH : ∀ s U, (H s U).part D.quiet = 0) :
    (fun U => u.restriction (restore P Φ ω H K U)) =
      restore P (Φ ∘ u.e) (ω ∘ u.e)
        (fun s U => u.restriction (H s U)) (fun s U => u.restriction (K s U)) := by
  funext U
  have hz : (Mach D (fun i => Φ i U) + ∑ s, H s U).part D.quiet = 0 := by
    simp only [Poly.part_plus, mute, Poly.part_sum, hH, Finset.sum_const_zero, add_zero]
  have hb (s : Box n) : u.restriction (bar P.activities D U s) =
      bar P.activities B U s := by
    change u.restriction (Poly.send D.quiet _) = Poly.send B.quiet _
    rw [← u.quiet, restriction_send]
  unfold restore
  rw [u.smul, map_mul, u.pass_restrict hz]
  simp only [map_add, map_sum, restriction_mach]
  rw [restriction_field]
  simp only [map_add, hb, restriction_mach, Function.comp_def]

/-- Restriction retains the same physical representation and every original
gas term. The existing input majorants pay the output with coefficient one. -/
theorem restriction_served (P : Rep G n)
    (Φ : W → Config G n → ℂ) (ω : W → Box n → Config G n → ℂ)
    (Z : Config G n → Poly D) (o : W → Site n)
    (w : W → ℝ) (hw : ∀ i, 0 ≤ w i) {e c : ℝ}
    (h : Served P Φ ω Z o w e c) :
    Served P (Φ ∘ u.e) (ω ∘ u.e) (fun U => u.restriction (Z U))
      (o ∘ u.e) (w ∘ u.e) e c := by
  obtain ⟨H, K, hCarton, hRegular, hForced, rfl⟩ := h
  exact ⟨fun s U => u.restriction (H s U), fun s U => u.restriction (K s U),
    restriction_carton u o hCarton, restriction_towed u w hw hRegular,
    restriction_towed u w hw hForced,
    restriction_restore u P Φ ω H K (fun s U => (hCarton.exp s).1.sil U)⟩

/-- Every added exclusion on an unchanged alphabet is a native identity
embedding into the unrestricted stock census. -/
def intoStock (B : Census V) : Names B (Stock.census V) where
  e := Function.Embedding.refl V
  visible _ := Finset.mem_univ _

/-- Concrete source-to-consumer form for the Deck output and later Replica
mouth: only forbidden modes are removed; singleton data, sites and weights
are literally unchanged. -/
theorem stock_served (B : Census V) (P : Rep G n)
    (Φ : V → Config G n → ℂ) (ω : V → Box n → Config G n → ℂ)
    (Z : Config G n → Poly (Stock.census V)) (o : V → Site n)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) {e c : ℝ}
    (h : Served P Φ ω Z o w e c) :
    Served P Φ ω (fun U => (intoStock B).restriction (Z U)) o w e c :=
  restriction_served (intoStock B) P Φ ω Z o w hw h

end YM.Integration.NativeRestrictionServed
