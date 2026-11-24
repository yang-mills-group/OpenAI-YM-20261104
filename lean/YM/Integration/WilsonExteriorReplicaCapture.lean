import YM.Integration.IntrinsicProductCompactness
import YM.Integration.ActualFoundryDetectorReadout

/-! Alternating trains of original signed Wilson products with independent exterior fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonExteriorReplicaCapture

open Function Filter Lattice Wilson Cells Extraction OPE OPE.Log OPE.Cards
open Frontier6.Road StressFlux.Matching
open IntrinsicPhysicalCell ActualFoundryDetectorSource WilsonMixedPlacement WilsonExteriorTrains
open scoped Classical BigOperators Topology

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ}

/-- The unexpanded physical product minus the represented terminal report of that very product. -/
def discrepancy (H : C.Makes) (D b j : ℕ) (x : I → Cover)
    (v : (i : I) → C.label (d i)) (w : ℕ × ℕ) : Config G (C.side w.1 w.2) → ℂ :=
  leafGap C j D d x v w.1 w.2
    (IntrinsicProductCompactness.value (D := D) H b w (leaves C j d x v w.1 w.2))

theorem discrepancy_paid {H : C.Makes} {D b j : ℕ} {x : I → Cover}
    {v : (i : I) → C.label (d i)} {w : ℕ × ℕ} {fee : ℝ}
    (h : Observed H b j D x v w fee) :
    PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) fee (discrepancy H D b j x v w) := by
  obtain ⟨ho, hl, _, hi, hr⟩ := h
  unfold discrepancy
  rw [IntrinsicProductCompactness.value_eq H ho hl]
  exact ⟨hl, hi, hr⟩

/-- Even positions are adjointed in the original thermal integral. -/
def alternate {n : Side} (s : ℕ) (F : Config G n → ℂ) : Config G n → ℂ :=
  if s % 2 = 0 then fun U => star (F U) else F

theorem alternate_paid {N p k : ℕ} {β a : ℝ} {F : Config G (C.side N p) → ℂ}
    (h : PaidAt C.S N p k β a F) (s : ℕ) :
    PaidAt C.S N p k β a (alternate s F) := by
  unfold alternate
  split
  · exact h.stars
  · exact h

/-- One normalized Wilson expectation containing every alternating complete
discrepancy and every independent exterior factor of every copy. -/
def reading (C : Family G) (w : ℕ × ℕ) (b t copies : ℕ) (y : E → E4)
    (F : Config G (C.side w.1 w.2) → ℂ) (de : E → ℕ) (e : (i : E) → C.label (de i)) : ℂ :=
  moment (C.beta w.1 w.2) (fun U =>
    (∏ i : Fin (2 * copies) × Unit, alternate i.1.val F
      (translate (ceilSite C w.1 w.2 (train C b t i.1 0)) U)) *
    ∏ i : Fin (2 * copies) × E, alternate i.1.val (C.O w.1 w.2 (e i.2) 0)
      (translate (ceilSite C w.1 w.2 (train C b t i.1 (y i.2))) U))

theorem placed (H : C.Makes) {b q n Q t copies : ℕ} {w : ℕ × ℕ} {hbq : b ≤ q} {hqn : q ≤ n}
    {y : E → E4} (p : PlacementAt C b q n hbq hqn (fun _ : Unit => 0) y
      (2 * copies) t w.1 w.2) (hqQ : q ≤ Q) {fee : ℝ} (A : E → ℝ)
    {F : Config G (C.side w.1 w.2) → ℂ}
    (hs : PaidAt C.S w.1 w.2 Q (C.beta w.1 w.2) fee F)
    (de : E → ℕ) (e : (i : E) → C.label (de i))
    (ht : ∀ i, PaidAt C.S w.1 w.2 n (C.beta w.1 w.2) (A i) (C.O w.1 w.2 (e i) 0)) :
    ‖reading C w b t copies y F de e‖ ≤ (fee * ∏ i, A i) ^ (2 * copies) := by
  have h := p.price H hqQ hs.live (fun _ : Unit => fee) A
    (fun i => alternate i.1.val F) (fun i => alternate i.1.val (C.O w.1 w.2 (e i.2) 0))
    (fun i => alternate_paid (C := C) hs i.1.val)
    (fun i => alternate_paid (C := C) (ht i.2) i.1.val)
  simpa only [reading, Fintype.prod_unique] using h

/-- The exterior level and cost, and the canonical central fee and levels,
precede the replica count. The regulator is sent to its continuum limit for
each train spacing. The physical exterior positions are independent of the
shrinking inner scale. -/
theorem engineering {α : Type*} {l : Filter α} {T : α → ℝ}
    (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (hT : Tendsto T l atTop) (D : ℕ) (v : α → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE l T (fun s => v s i k) (-(d i : ℝ)))
    (y : E → E4) (hy : Injective (Sum.elim (fun _ : Unit => 0) y)) (de : E → ℕ)
    (R : E → ℝ) (hR : ∀ i, 0 < R i) (δ : ℝ) (hδ : 0 < δ) :
    ∃ outer n : ℕ, ∃ A : E → ℝ, (∀ i, 0 ≤ A i) ∧
    ∃ b m j : α → ℕ, ∃ h a c : ℝ, Height C.S l T b h ∧ Height C.S l T m a ∧
      Height C.S l T j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
    ∃ fee : α → ℝ, RateLE l T fee (-(D : ℝ) - 1 / 32) ∧
    ∀ᶠ s in l, ∀ (x : I → Cover), Plot C (b s) (m s) (j s) x →
    ∀ copies : ℕ, ∀ᶠ t : ℕ in atTop, ∀ᶠ w : ℕ × ℕ in f.fuse,
    ∀ (e : (i : E) → C.label (de i)), (∀ i, ‖e i‖ ≤ R i) →
      ‖reading C w outer t copies y (discrepancy F.room.cutoff D (b s) (j s) x (v s) w) de e‖ ≤
        (fee s * ∏ i, (A i * C.S.a n ^ (-(de i : ℝ) - δ) + 1)) ^ (2 * copies) := by
  obtain ⟨n₀, A, hA, ext⟩ := exterior_bounds F de R hR δ hδ
  obtain ⟨outer, _, q, _, n, hn, hbq, hqn, hp⟩ :=
    placements (C := C) f (fun _ : Unit => 0) y hy 0 0 n₀
  obtain ⟨b, m, j, h, a, c, hb, hm, hj, hh, ha, ha₁, hc, fee, he, seen⟩ :=
    IntrinsicPhysicalCell.engineering F facility anchor hT D v hv
  refine ⟨outer, n, A, hA, b, m, j, h, a, c, hb, hm, hj, hh, ha, ha₁, hc, fee, he, ?_⟩
  filter_upwards [seen, hb.grows.eventually_ge_atTop q] with s hs hq
  intro x hx copies
  filter_upwards [hp (2 * copies)] with t ht
  filter_upwards [ht, hs x hx, ext n ((le_max_right q n₀).trans hn) 1 one_pos] with w hpw hw hE
  obtain ⟨p⟩ := hpw
  intro e hext
  exact placed F.room.cutoff p hq _ (discrepancy_paid hw) de e (hE e hext)

end YM.Integration.WilsonExteriorReplicaCapture
