import YM.GradedFar.Continuation.Pivot

/-!
# Decode on these very same measured rows
-/
namespace YM.FVA2.GradedFar.Continuation.Margin
noncomputable section
open Filter Set Real Topology Function PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Window
open Stretch (till Deep Stiff)
open scoped Topology BigOperators Classical Matrix
variable {G : Gauge} {n h : ℕ} {N : WilsonPrescription G} {d : Fin n → ℕ}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

local notation "g" => gYM G
variable {I : Type} (t : ℝ → ℝ) {c C η B : ℝ} (hb : 0<B) (hc : 0<c) (hC : c ≤ C)
  {p P : ℕ} (ht : Tendsto (fun r => t r/gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
  {Z : ChangeAt G} {D0 : TagAt G (fun _ : Fin 1 => h) I h} {F0 : ReadAt G d (fun _ : Fin 1 => h) I}
  {packet : PacketAt G d I h}
  (hp : Stretch.Deep p P B h h η) (hη : 0<η)
  {K : Set (Points n)} (hK : IsCompact K) (hx : K ⊆ conf n)
  {R v L : ℝ}

lemma sum_rows (d : Sec G h → ℂ) (hd : ∃ δ : Sec G h →ₗ[ℂ] ℂ, d = δ) (a : Sec G h) :
    d a = ∑ b : Toon G h, coord b a * d (theory b) := by
  obtain ⟨δ,rfl⟩ := hd
  nth_rw 1 [← reconstructed a]; rw [map_sum]; simp_rw [_root_.map_smul, smul_eq_mul]

-- use linearity applied in the center of a measured moment.
theorem decode (w : Window) (i : I) (hw : IsUnit (measuredAt Z D0 w i))
    (bound : ∀ a b, ‖(measuredAt Z D0 w i)⁻¹ a b‖ ≤ R*w.Stretch^h)
    (hc : ∀ b : Toon G h, ∃ δ : Sec G h →ₗ[ℂ] ℂ, DCoat Z D0 w i RootG (probe b) = δ) (a₁ a₂ : Sec G h)
    (ha : ∀ b : Toon G h, ‖DCoat Z D0 w i RootG (probe b) a₁-DCoat Z D0 w i RootG (probe b) a₂‖ ≤ L) :
    Ball ((Fintype.card (Toon G h))*R*w.Stretch^h*L) (a₁-a₂) := by
  let F := measuredAt Z D0 w i
  let x a := coord a (a₁-a₂)
  let y := F*ᵥ x
  have hh : F⁻¹*ᵥ y=x := by
    unfold y; rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hw),Matrix.one_mulVec]
  have hf (k : Toon G h) : ‖y k‖ ≤ L := by
    obtain ⟨δ,hv⟩ := hc k
    have eq : y k=δ (a₁-a₂) := by
      rw [
        ← reconstructed (a₁-a₂)]
      rw [map_sum]; simp_rw [_root_.map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      change DCoat Z D0 w i RootG (probe k) (theory j) * x j = _
      rw [hv]; exact mul_comm ..
    rw [eq,map_sub]
    simpa only [hv] using ha k
  intro b
  change ‖x b‖ ≤ _
  rw [← hh]
  apply le_trans (b := ∑ _ : Toon G h, R*w.Stretch^h*L) _ ?_
  swap
  · exact le_of_eq (by simp; ring)
  refine norm_sum_le_of_le _ fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul (bound b j) (hf j) (norm_nonneg _) (le_trans (norm_nonneg _) (bound b j))

include H hb hc hC ht hp hη hK hx
-- narrow hypotheses to same enrollment; packet on each near only (any viewer dependence allowed here).
theorem behind (hd : ∀ᶠ (w : Window) in windows (band G c C B),
      ∀ i (b : Toon G h), ∃ δ : Sec G h →ₗ[ℂ] ℂ, DCoat Z D0 w i RootG (probe b) = δ)
    (frame : ReplacementAt N M h Z (upper G C B) t p)
    (full : RoundedAt N F0 (upper G C B) K {RootG} t p)
    (hsingle : RoundedAt N D0 (upper G C B) {0} {RootG} t p)
    (spatial : Spatial Z F0 D0 packet (upper G C B) v L R K {RootG})
    (hs : ∀ b : Toon G h, Within R (probe b))
    (hv : 0 ≤ v) (hbgt : Stretch.Stiff B P η v) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ (w : Window) in windows (band G c C B), ∀ i x, x∈K →
      ∀ u : Inputs G d, Within L u →
        Ball (D*g w.len^P*w.Stretch^(-η)) (packet w.len i x u - cActual N x u h p (t w.len)) := by
  have Hη : Stretch.Deep p P B (∑ i : Fin 1, h) h η := by simpa using hp
  let rset : Set (Points 1) := {RootG}
  have hx1 : rset ⊆ O.Enh.Outside 1 := singleton_subset_iff.mpr ok_wall
  obtain ⟨D,hD,hr⟩:= tolerance H t hK hx isCompact_singleton hx1 ht hc hC hb Hη hv hbgt
    (fun _=>frame) full hsingle spatial
  have hF : ({0} : Set (Points 1)) ⊆ conf 1 := singleton_subset_iff.mpr (fun i j h => Subsingleton.elim ..)
  obtain ⟨Q,hQ,hq⟩ := pivot_safe H t hb hc hC ht hp hη (fun L R => paid_first H Z _ t _ D0 isCompact_singleton
    hF isCompact_singleton hx1 ((paid_reading simple t ht).mono fun i hi => hi.2.2.2) (fun _=>frame) hsingle L R)
  let K₀ : ℝ := (Fintype.card (Toon G h):ℝ)*Q*D
  refine ⟨max K₀ 1,lt_max_of_lt_right zero_lt_one,?_⟩
  filter_upwards [hr,hq,hd,(windows_short _).eventually (positive_g simple)] with w hw hm Hx hg
  intro i x hW u hU
  let Y v:= YCoat Z F0 w i x RootG u v
  let F v:= DCoat Z D0 w i RootG v
  let c1 := packet (Window.len w) i x u; let c2 := cActual N x u h p (t (Window.len w))
  let W := till G P h η w
  have he z : ‖F (probe z) c1 - F (probe z) c2‖ ≤ D*W := by
    have h := hw i x hW RootG (mem_singleton _) u hU (probe z) (hs z) (theory z) (ball_basis z)
    let E := Y (probe z); let T := F (probe z)
    calc
      _ ≤ ‖T c1-E‖+‖E-T c2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ D*W := by
        apply le_trans _ h
        rw [norm_sub_rev (T c1) E]
        gcongr ?_ + _
        refine le_add_of_nonneg_left ?_
        unfold weigh; positivity
  have hx := decode (Z:=Z) (D0:=D0) w i (hm i).1 (hm i).2 (Hx i) c1 c2 he
  have hp : 0 < Window.Stretch w := exp_pos _
  intro b; apply (hx b).trans
  have eq: Window.Stretch w^h * W = g (Window.len w)^P * Window.Stretch w^(-η) := by
    unfold W till; change Window.Stretch w^h * (g (Window.len w)^P * Window.Stretch w ^ (-((h:ℝ)+η)))=_
    rw [← Real.rpow_natCast (Window.Stretch w) h, mul_left_comm _ (g (Window.len w)^P),← rpow_add hp,
      show (h:ℝ)+(-((h:ℝ)+η))= -η by ring]
  calc _ = K₀*(Window.Stretch w^h*W) := by unfold K₀; ring
       _ = K₀*g (Window.len w)^P*Window.Stretch w^(-η) := by rw [eq]; ring
       _ ≤ _ := by
         gcongr
         exact le_max_left ..
end
end YM.FVA2.GradedFar.Continuation.Margin

