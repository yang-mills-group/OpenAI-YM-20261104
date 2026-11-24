import YM.SchemeConversionRG11.Detector.Search

/-! Position-frame solve commutes with enlarging the data into coherent higher-horizon data.
This is a theorem in the same fixed choice of nested menu, on free-leading series. Include
the version for varying regulator leading frames *converging* to the free chart.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Detector.Poll
open Function Filter Maxwell Issue Series Pert.Position Horizon Affine Orbit
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {d e f p : ℕ}
variable {P : Poll F d} {Q : Poll F e} {h : d ≤ e} {A : Issue F d} {B : Issue F e}

-- exact meanings of including a set of previous tests
lemma growing (u : Section F d) (h : d ≤ e) (hk : e ≤ f) : grow hk (grow h u) = grow (h.trans hk) u := by
  suffices he : (fun i ↦ incl F hk (incl F h (u.p i))) = fun i ↦ incl F (h.trans hk) (u.p i) by
    unfold grow; rw [he]
  exact funext fun _ ↦ incl_repeat ..

lemma Carries.self (P : Poll F d) : Carries P P le_rfl := by
  have H (w : Section F d) : grow le_rfl w = w := by unfold grow; simp_rw [incl_self]
  intro a; simp only [restr_self,H]

lemma Carries.trans {S : Poll F f} {h' : e ≤ f} (hw : Carries P Q h) (hz : Carries Q S h') :
    Carries P S (h.trans h') := by
  intro a; rw [← restr_compose F h h', hz]
  have he (s) : a (grow (h.trans h') s) = (a ∘ grow (F:=F) h') (grow h s) := by rw [comp_apply,growing]
  simp_rw [he]; exact hw (a ∘ grow h')

/-- Single schedule coherent at every horizon. -/
def FamilyMenu (c : (d : ℕ) → Poll F d) := ∀ (i j : ℕ), ∀ h : i ≤ j, Carries (c i) (c j) h

theorem menu_of_rank (H : ∀ d, Frozen F d) : ∃ c : (d : ℕ) → Poll F d, FamilyMenu c := by
  obtain ⟨c,hc⟩ := sequence H
  refine ⟨c,fun i j h ↦ ?_⟩
  induction h with
  | refl => exact Carries.self _
  | step h ih => exact ih.trans (hc _)

private def counted (F : Labels.Frames G) (d : ℕ) (t : Section F d) (A : Issue F d) (j : ℕ) :=
  (A _ t.f j t.p).re
lemma Carries.test (hw : Carries P Q h) (v : Compatible p A B h) :
    Through p (fun i ↦ restr F h (Q.fares B i)) (P.fares A) := by
  intro i hi; rw [fares,fare_at]
  have ht (t : Section F d) : counted F e (grow h t) B i = counted F d t A i :=
    congrArg Complex.re (congrArg (fun x : Tape F d t.r ℂ ↦ x t.p) (v t.r t.f i hi))
  change restr F h (Q.pointer (fun i' ↦ counted F e (Q.table i') B i)) = P.fareL _
  rw [hw (fun s ↦ counted F e s B i), fare_at]; simp_rw [ht]; rfl

lemma scan_baseline (P : Poll F d) : scan P (P.blank,0) = P.pointer (prices P P.blank) := by
  unfold scan; rw [comp_apply, fare_at]
  exact congrArg P.pointer (congrArg P.prices (funext fun t ↦ Tape.put_zero (P.blank t)))

lemma Carries.transfer (hw : Carries P Q h) : (fun i ↦ restr F h (Q.target i)) = P.target := by
  have he : restr F h (scan Q (Q.blank,0)) = scan P (P.blank,0) := by
    let C (j m : ℕ) (t : Test m) : Series (Tape F j m ℂ) := fun _ ↦ gaussian F j t
    have hv := hw.test (p:=0) (A:= C d) (B := C e) (fun _ t _ _ ↦ gauss_includes t h) |>.zero
    rw [scan_baseline,scan_baseline]
    exact hv
  have H (i : ℕ) : restr F h (Q.target i) = P.target i := by
    unfold target; let g := fun _ : ℝ ↦ Q.scan (Q.blank,0)
    have ht := (record_represents (n:=i) (show ContDiffAt ℝ ω g 0 from contDiffAt_const)).linear
      (F:=Buffer F d) (restr F h)
    rw [show (restr F h ∘ g) = fun _ ↦ P.scan (P.blank,0) from funext (fun _ ↦ he)] at ht
    exact ht.unique (record_represents contDiffAt_const) i le_rfl
  exact funext H

theorem lower_press {X : Series (Buffer F d)} {Y : Series (Buffer F e)}
    (hb : Compatible p A B h) (hy : Q.Pinned B Y p)
    (hk : Through p (fun j ↦ restr F h (Y j)) X) (hu : Carries P Q h) : P.Pinned A X p := by
  apply Through.trans ((hu.test (hb.moves h hk)).symm)
  rw [← hu.transfer]
  exact fun i hi ↦ congrArg _ (hy i hi)

lemma matches_frame (hw : Carries P Q h) (hA : Twist A) (hB : Twist B) (v : Compatible p A B h) :
    Through p (fun i ↦ restr F h (Q.press B i)) (P.press A) := by
  have he : Through p (fun i ↦ restr F h (Q.press B i)) _ := Through.rfl
  apply P.unique_frame _ hA (lower_press v (Q.captures hB p) he hw)
  rw [Q.starts_zero hB,map_zero]

def Crossing (M : (d : ℕ) → Issue F d) (p h : ℕ) :=
  ∀ (i j : ℕ), ∀ m : i ≤ j, j ≤ h → Compatible p (M i) (M j) m

theorem across {R : (d : ℕ) → Poll F d} (hR : FamilyMenu R) {M : ∀ i, Issue F i}
    (hs : ∀ i ≤ d, Twist (M i)) (H : Crossing M p d) :
    Guided p (fun d ↦ (R d).press (M d)) d := by
  intro i j h hj; exact matches_frame (hR i j h) (hs i (h.trans hj)) (hs j hj) (H i j h hj)

section regulator
variable {I : Type*} {l : Filter I}

theorem reaches {A : I → Issue F d}
    (hA : Tendsto (fun i ↦ P.getTest (A i) 0) l (𝓝 P.blank)) :
    (Tendsto (fun i ↦ P.press (A i) 0) l (𝓝 0)) ∧ (∀ᶠ i in l, ∀ p, P.Pinned (A i) (P.press (A i)) p) := by
  have hp : Reports P.scan P.blank 0 P.solution := Classical.choose_spec P.discovers
  refine ⟨?_, (hA.eventually P.eventually_presses).mono (fun _ h ↦ h.2 _ rfl)⟩
  simp_rw [press, liftJet_zero]
  rw [← hp.fixes]; exact hp.diff.continuousAt.tendsto.comp hA

/-- Finite-order coherence once finite demands are admitted. Don't quantify over unrelated
 sequences of regulator limit choices; tests/leading frame lie eventually in the SAME chart. -/
theorem eventually_coherent {A : I → Issue F d} {B : I → Issue F e}
    (hA : Tendsto (fun i ↦ P.getTest (A i) 0) l (𝓝 P.blank))
    (hB : Tendsto (fun i ↦ Q.getTest (B i) 0) l (𝓝 Q.blank))
    (he : ∀ᶠ i in l, Compatible p (A i) (B i) h) (hw : Carries P Q h) :
    ∀ᶠ i in l, Through p (fun j ↦ restr F h (Q.press (B i) j)) (P.press (A i)) := by
  obtain ⟨hg, hg'⟩ := reaches hB
  obtain ⟨hk, hk'⟩ := reaches hA
  have ht : Tendsto (fun i ↦ restr F h (Q.press (B i) 0)) l (𝓝 0) :=
    map_zero (restr F h) ▸ ((restr F h).continuous.continuousAt.tendsto.comp hg)
  filter_upwards [(hA.prodMk_nhds ht |>.prodMk_nhds hk).eventually P.close_inj,hk',hg',he] with i hu hv hs hi
  exact hu _ _ _ rfl rfl rfl _ ((lower_press hi (hs p) Through.rfl hw).trans (hv p).symm)
end regulator
end YM.SchemeConversionRG11.Detector.Poll
