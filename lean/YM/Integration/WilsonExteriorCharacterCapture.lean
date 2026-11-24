import YM.Integration.WilsonExteriorReplicaCapture
import YM.OPE.Loom.Traffic

/-! Ground-algebra bounds for the actual intrinsic report against independent
separated physical exterior fields, uniform over a given exterior clearance. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonExteriorCharacterCapture

open Function Filter Lattice Wilson Cells Extraction OPE OPE.Log OPE.Cards Frontier6.Road
open IntrinsicPhysicalCell IntrinsicProductCompactness WilsonExteriorReplicaCapture ActualFoundryDetectorSource
open scoped Classical BigOperators Topology

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ}

def wordError (F : Spec.Final C f S) (D j : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (z : C.label D) (y : E → E4) (de : E → ℕ) (e : (i : E) → C.label (de i)) :
    F.α.unselected.algebra :=
  let inner (i : I) : C.book.Token := ⟨d i, v i⟩
  let outer (i : E) : C.book.Token := ⟨de i, e i⟩
  viewing F (beside (C.S.gridPoint j ∘ x) y) (beside inner outer) -
    viewing F (beside (fun _ : Unit => (0 : E4)) y) (beside (fun _ : Unit => ⟨D, z⟩) outer)

private theorem register_leaves (j : ℕ) (x : I → Cover) (v : (i : I) → C.label (d i))
    (w : ℕ × ℕ) :
    register C j x (germ (frozen C (fun i => ⟨d i, v i⟩))) w.1 w.2 =
      leaves C j d x v w.1 w.2 := by
  funext U
  rw [germ_here]
  simp only [leaves, Finset.prod_apply, frozen]

/-- The counterterm is a cluster point of the very same original Wilson report.
The original ground moment limit controls all characters of the common operator. -/
theorem ground (F : Spec.Final C f S) (services : Services C f S) {D b o u buffer n j : ℕ}
    {x : I → Cover} (v : (i : I) → C.label (d i)) (de : E → ℕ) (e : (i : E) → C.label (de i))
    (y : E → E4) (ho : o ≤ j) (hc : Screen (C.S.gridPoint j ∘ x))
    (hy : Apart (2 * C.S.a u) y) (hxy : ApartFrom (2 * C.S.a o) (fun _ : Unit => (0 : E4)) y)
    (hs : Injective (beside (C.S.gridPoint j ∘ x) y))
    (hall : Hall C.S o u b buffer n 1 (Fintype.card E)) {l : Filter (ℕ × ℕ)} [l.NeBot]
    (hl : l ≤ f.fuse) {z : C.label D}
    (hz : Tendsto (fun w : ℕ × ℕ => value (D := D) F.room.cutoff b w (leaves C j d x v w.1 w.2)) l (𝓝 z))
    {fee : ℝ} (hO : ∀ᶠ w in l, Observed F.room.cutoff b j D x v w fee)
    {A : E → ℝ} (hE : Prepared (C := C) (fun i => ⟨de i, e i⟩) f n A) :
    ‖wordError F D j x v z y de e‖ ≤ fee * ∏ i, A i := by
  let input (i : I) : C.book.Token := ⟨d i, v i⟩
  let outer (i : E) : C.book.Token := ⟨de i, e i⟩
  have hfill : ∀ᶠ w : ℕ × ℕ in l, PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) fee
      (register C j x (germ (frozen C input)) w.1 w.2 -
        C.O w.1 w.2 (value (D := D) F.room.cutoff b w (leaves C j d x v w.1 w.2)) 0) := by
    filter_upwards [hO] with w hw
    rw [show register C j x (germ (frozen C input)) w.1 w.2 = leaves C j d x v w.1 w.2 from
      register_leaves j x v w]
    exact discrepancy_paid hw
  exact OPE.current_space F services.schedule (frozen C input) ho hc hy hxy hs hall hl hz
    (fun _ => tendsto_const_nhds) hfill hE

private theorem small (S₀ : Schedule) (a c : ℝ) (hc : 0 < c) (base : ℕ) :
    ∃ k : ℕ, base ≤ k ∧ a * S₀.a k < c := by
  have h : Tendsto (fun k => a * S₀.a k) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := a)).mul S₀.shrinks
  exact ((eventually_ge_atTop base).and (h.eventually (gt_mem_nhds hc))).exists

/-- The radius and directional data of the exterior may vary with the inner scale.
The original purchased regulator levels determine the two required spatial clearances. -/
theorem windows {α : Type*} {l : Filter α} {T : α → ℝ} (F : Spec.Final C f S)
    (facility : Facilities C f S) (anchor : I) (hT : Tendsto T l atTop) (D : ℕ)
    (v : α → (i : I) → C.label (d i)) (hv : ∀ i k, RateLE l T (fun s => v s i k) (-(d i : ℝ)))
    (de : E → ℕ) (R : E → ℝ) (hR : ∀ i, 0 < R i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∃ A : E → ℝ, (∀ i, 0 ≤ A i) ∧
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
    ∃ fee : α → ℝ, RateLE l T fee (-(D : ℝ) - 1 / 32) ∧
    ∀ᶠ s in l, ∀ o u buffer n : ℕ, n₀ ≤ n → Hall C.S o u (b s) buffer n 1 (Fintype.card E) →
    ∀ (x : I → Cover), Plot C (b s) (m s) (j s) x → Screen (C.S.gridPoint (j s) ∘ x) →
    ∀ (y : E → E4), Apart (2 * C.S.a u) y → ApartFrom (2 * C.S.a o) (fun _ : Unit => (0 : E4)) y →
      Injective (beside (C.S.gridPoint (j s) ∘ x) y) →
    ∀ (e : (i : E) → C.label (de i)), (∀ i, ‖e i‖ ≤ R i) →
    ∀ (l' : Filter (ℕ × ℕ)), l'.NeBot → l' ≤ f.fuse → ∀ z : C.label D,
      Tendsto (fun w : ℕ × ℕ => value (D := D) F.room.cutoff (b s) w
        (leaves C (j s) d x (v s) w.1 w.2)) l' (𝓝 z) →
      ∀ χ : Viewers F, ‖glance F χ (wordError F D (j s) x (v s) z y de e)‖ ≤
        fee s * ∏ i, (A i * C.S.a n ^ (-(de i : ℝ) - δ) + 1) := by
  obtain ⟨n₀, A, hA, ext⟩ := exterior_bounds F de R hR δ hδ
  obtain ⟨b, m, j, h, a, c, hb, hm, hj, hh, ha, ha₁, hc, fee, he, seen⟩ :=
    IntrinsicPhysicalCell.engineering F facility anchor hT D v hv
  refine ⟨n₀, A, hA, b, m, j, h, a, c, hb, hm, hj, hh, ha, ha₁, hc, fee, he, ?_⟩
  filter_upwards [seen] with s paid
  intro o u buffer n hn hall x hx hscreen y hy hxy hsep e hE l' live sub z hz χ
  letI := live
  have ht : Prepared (C := C) (fun i => ⟨de i, e i⟩) f n
      (fun i => A i * C.S.a n ^ (-(de i : ℝ) - δ) + 1) :=
    ⟨fun i => (ext n hn 1 one_pos).mono fun w hw => hw e hE i⟩
  have hoJ : o ≤ j s :=
    ((hall.first.trans hall.third).trans hx.first).trans ((Nat.le_succ _).trans hx.last)
  exact (glance_bound F χ _).trans (ground F facility.toServices (v s) de e y hoJ hscreen
    hy hxy hsep hall sub hz ((paid x hx).filter_mono sub) ht)

/-- The exterior levels and label bank are bought before the true inner
scale, the positions of the exterior, the cluster point, and the character. -/
theorem menu {α : Type*} {l : Filter α} {T : α → ℝ} (F : Spec.Final C f S)
    (facility : Facilities C f S) (anchor : I) (hT : Tendsto T l atTop) (D : ℕ)
    (v : α → (i : I) → C.label (d i)) (hv : ∀ i k, RateLE l T (fun s => v s i k) (-(d i : ℝ)))
    (de : E → ℕ) (R : E → ℝ) (hR : ∀ i, 0 < R i) (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ n : ℕ, ∃ A : E → ℝ, (∀ i, 0 ≤ A i) ∧
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
    ∃ fee : α → ℝ, RateLE l T fee (-(D : ℝ) - 1 / 32) ∧
    ∀ᶠ s in l, ∀ (x : I → Cover), Plot C (b s) (m s) (j s) x → Screen (C.S.gridPoint (j s) ∘ x) →
    ∀ (y : E → E4), Apart η y → ApartFrom η (fun _ : Unit => (0 : E4)) y →
      Injective (beside (C.S.gridPoint (j s) ∘ x) y) →
    ∀ (e : (i : E) → C.label (de i)), (∀ i, ‖e i‖ ≤ R i) →
    ∀ (l' : Filter (ℕ × ℕ)), l'.NeBot → l' ≤ f.fuse → ∀ z : C.label D,
      Tendsto (fun w : ℕ × ℕ => value (D := D) F.room.cutoff (b s) w
        (leaves C (j s) d x (v s) w.1 w.2)) l' (𝓝 z) →
      ∀ χ : Viewers F, ‖glance F χ (wordError F D (j s) x (v s) z y de e)‖ ≤
        fee s * ∏ i, (A i * C.S.a n ^ (-(de i : ℝ) - δ) + 1) := by
  obtain ⟨n₀, A, hA, b, m, j, h, a, c, hb, hm, hj, hh, ha, ha₁, hc, fee, he, paid⟩ :=
    windows F facility anchor hT D v hv de R hR δ hδ
  obtain ⟨o, _, ho⟩ := small C.S 2 η hη 0
  obtain ⟨u, hou, hu⟩ := small C.S 10 (C.S.a o) (C.S.a_pos _) o
  obtain ⟨n, hn, hn'⟩ := small C.S ((Fintype.card E : ℝ) * 6) (C.S.a u) (C.S.a_pos _) (max u n₀)
  refine ⟨n, A, hA, b, m, j, h, a, c, hb, hm, hj, hh, ha, ha₁, hc, fee, he, ?_⟩
  filter_upwards [paid, hb.grows.eventually_ge_atTop u] with s hs hus
  have hall : Hall C.S o u (b s) u n 1 (Fintype.card E) := by
    refine ⟨hou, le_rfl, hus, (le_max_left ..).trans hn, ?_, ?_⟩
    · simpa only [Nat.cast_one, one_mul] using (show 2 * (5 * C.S.a u) < C.S.a o by linarith)
    · convert hn' using 1
      ring
  have hsmall : 2 * C.S.a u < η := by linarith [C.S.a_pos u]
  intro x hx hscreen y hy hxy
  exact hs o u u n ((le_max_right ..).trans hn) hall x hx hscreen y
    (fun i k hk => hsmall.trans (hy i k hk)) (fun i k => ho.trans (hxy i k))

end YM.Integration.WilsonExteriorCharacterCapture
