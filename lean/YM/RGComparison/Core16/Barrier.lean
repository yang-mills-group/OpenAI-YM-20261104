import YM.RGComparison.Core16.HistoryIntegral
import YM.Work.E02
import YM.Work.F01

/-!
# Multistep action barrier (Wilsonian conditional expansion)

Unmarked estimate, with all tags, not a perturbative estimate. For the history in the actual tree
slices, simultaneous control of the coarse plaquettes and ALL integration links by the top
full Wilson energy and the chain of prediction errors. In this max (per-link) control, no torus
size cost. Needs the geometric (`Bid.Larger`) condition. Does not cost probability that any
particular link will be bad *after integrating*, nor assert the coarse field itself is flat.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Push.BetaTransport Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n c f : Side}
variable (S : StepData c f)

/-- The combined cap includes noise energy at *every* intermediate step with actual positive
κ. No offsets! -/
def action (d : Descent n c) := d.account (G := G) 1

lemma account_nonnegative (d : Descent n c) {β : ℕ → ℝ} (hβ : ∀ i ≤ d.depth, 0 ≤ β i)
    (t : d.Tags) (V : Config G c) (x : Fields G d) : 0 ≤ d.account β t V x := by
  induction d generalizing β with
  | nil => exact mul_nonneg (hβ _ (Nat.zero_le _)) (energy_nonneg V)
  | push S T d ih =>
    exact add_nonneg (mul_nonneg (hβ _ (Nat.succ_le_succ (Nat.zero_le _)))
      ((energy_estimate S _).nonneg V)) (ih (β := upβ β) (fun i hi => hβ _ (Nat.succ_le_succ hi)) ..)

lemma action_nonneg (d : Descent n c) (t : d.Tags) (V : Config G c) (x : Fields G d) :
    0 ≤ d.action t V x := account_nonnegative d (fun _ _ => zero_le_one) t V x

def macroCount (P : Patch) := ((Lattice.box (macroR P)).card : ℝ) * Fintype.card PlaqAxes

def faceUnit (G : Gauge) (K : KernelChoices) (P : Patch) : ℝ :=
    (qdc G K P.J).choose / (P.L.val : ℝ)^2 * macroCount P

def edgeUnit (G : Gauge) (K : KernelChoices) (P : Patch) : ℝ :=
    (Work.E02.answer G P.L P.J K).choose * macroCount P

def noiseUnit (K : KernelChoices) : ℝ := Real.sqrt (2/K.penalty)

/-- Downward bill at finite depth. No dependence on side except `Bid.Larger` premises. -/
def faceBill (G : Gauge) : {c : Side} → (d : Descent n c) → ℝ
  | _, .nil => Real.sqrt 2
  | _, .push S _ d => 4 * noiseUnit S.kernel + faceUnit G S.kernel S.patch * faceBill G d

/-- Return bill from the coarsest links up. Uses the same downward bill at all steps. -/
def edgeBill (G : Gauge) : {c : Side} → (d : Descent n c) → ℝ
  | _, .nil => 0
  | _, .push S _ d => edgeUnit G S.kernel S.patch * faceBill G d + noiseUnit S.kernel + edgeBill G d

variable (K : KernelChoices) (P : Patch)
lemma faceUnit_nonneg (G : Gauge) : 0 ≤ faceUnit G K P := by
  unfold faceUnit macroCount; have := (qdc G K P.J).choose_spec.1; positivity

lemma edgeUnit_nonneg (G : Gauge) : 0 ≤ edgeUnit G K P := by
  unfold edgeUnit macroCount; have := (Work.E02.answer G P.L P.J K).choose_spec.1; positivity

lemma faceBill_nonneg (G : Gauge) (d : Descent n c) : 0 ≤ faceBill G d := by
  induction d with
  | nil => exact Real.sqrt_nonneg _
  | push S T d ih =>
    rw [faceBill]; exact add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg (faceUnit_nonneg ..) ih)

lemma edgeBill_nonneg (G : Gauge) (d : Descent n c) : 0 ≤ edgeBill G d := by
  induction d with
  | nil => exact le_rfl
  | push S T d ih => exact add_nonneg (add_nonneg (mul_nonneg (edgeUnit_nonneg ..) (faceBill_nonneg G d))
      (Real.sqrt_nonneg _)) ih

def Room (G : Gauge) : {c : Side} → (d : Descent n c) → Prop
  | _, .nil => True
  | _, .push S _ d => Bid.Larger (G := G) S ∧ Room G d

lemma room_ok (d : Descent n c) (h : d.Room G) : d.OK G := by
  induction d with
  | nil => trivial
  | push _ _ _ ih => exact ⟨h.1.1, ih h.2⟩

def QuietFaces (V : Config G c) (δ : ℝ) : Prop := ∀ j, G.chord (faceValue V j) ≤ δ

def QuietLinks (V : Config G c) (δ : ℝ) : Prop := ∀ i, G.chord (V i) ≤ δ

private lemma port_bound {U : Config G f} {δ : ℝ} (h : QuietFaces U δ) (i : Site c) :
    port S i U ≤ macroCount S.patch * δ := by
  apply (Work.F01.port_le S U i).trans
  apply (Finset.sum_le_sum (g := fun _ => ∑ _ : PlaqAxes, δ) (fun x _ => Finset.sum_le_sum
    (f := fun p : PlaqAxes => G.chord (faceValue U (wrap f x + S.ratio.embed i, p))) (fun p _ => h _))).trans_eq
  simp [macroCount, mul_assoc]

section transition
variable {U : Config G f} {t : S.Choices} {V : Config G c} {r δ w : ℝ}
    (hr : 0 ≤ r) (hw : tagEnergy S t U V ≤ r^2)

include hr hw
lemma wire_bound (e : Edge (Site c)) : wire (S.prediction U t) V e ≤ noiseUnit S.kernel * r := by
  let W := wire (S.prediction U t) V e
  have hE (e : Edge (Site c)) := (link_estimate S).nonneg (V e * (S.prediction U t e)⁻¹)
  have he : linkEnergy S (V e * (S.prediction U t e)⁻¹) ≤ tagEnergy S t U V :=
    Finset.single_le_sum (fun i _ => hE i) (Finset.mem_univ _)
  let a := G.price (V e * (S.prediction U t e)⁻¹)
  change S.kernel.penalty * a ≤ _ at he
  have hW : W^2 = 2*a := G.chord_price _
  have hs := S.kernel.penalty_pos
  let A := noiseUnit S.kernel
  have hA : A^2 * S.kernel.penalty = 2 := by
    unfold A noiseUnit; rw [Real.sq_sqrt (by positivity), div_mul_cancel₀ _ hs.ne']
  apply (sq_le_sq₀ (show 0 ≤ W from G.chord_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)).mp
  apply le_of_mul_le_mul_right _ hs; change W^2 * _ ≤ (A*r)^2 * _
  rw [hW, mul_pow, mul_right_comm (A^2), hA]; nlinarith only [he,hw]

lemma downward (hp : 0 < S.likelihood U t) (hU : QuietFaces U δ) :
    QuietFaces V (4*noiseUnit S.kernel*r + faceUnit G S.kernel S.patch*δ) := by
  rintro ⟨x,p⟩
  have h := qdc G S.kernel S.patch.J
  apply (h.choose_spec.2 _ _ S rfl rfl U V x t (wraps S t hp x) p).2.trans
  have he : fuel (S.prediction U t) V x p ≤ 4*noiseUnit S.kernel*r := by
    unfold fuel
    apply (add_le_add (add_le_add (add_le_add (wire_bound S hr hw _) (wire_bound S hr hw _))
      (wire_bound S hr hw _)) (wire_bound S hr hw _)).trans_eq; ring
  refine add_le_add he ((mul_le_mul_of_nonneg_left (port_bound S hU x) ?_).trans_eq ?_)
  · exact div_nonneg h.choose_spec.1.le (sq_nonneg _)
  rw [← mul_assoc]; rfl

open Precision
lemma upward (hs : Bid.Larger (G := G) S) (T : Forest S.ratio) (ht : Stores.SliceSet S T U)
    (hp : 0 < S.likelihood U t) (hU : QuietFaces U δ) (hV : QuietLinks V w) (h₀ : 0 ≤ w) :
    QuietLinks U (edgeUnit G S.kernel S.patch*δ + noiseUnit S.kernel*r + w) := by
  intro e
  have h := Work.E02.answer G S.patch.L S.patch.J S.kernel
  let i := S.ratio.parent e.1
  have he : G.chord (U e * (replica S.ratio V e)⁻¹) ≤
      h.choose * port S i U + wire (S.prediction U t) V (i,e.2) := by
    apply (h.choose_spec.2 c f S rfl rfl rfl hs.2.1 hs.2.2 T U ht V e t (wraps S t hp _)).trans
    gcongr; split; exact G.chord_nonneg _; rfl
  refine (le_of_eq <| congrArg G.chord (inv_mul_cancel_right (U e) (replica S.ratio V e)).symm).trans
    ((G.chord_triangle _ _).trans ?_)
  refine add_le_add (he.trans (add_le_add ?_ (wire_bound S hr hw _))) ?_
  · exact (mul_le_mul_of_nonneg_left (port_bound S hU _) h.choose_spec.1.le).trans_eq (mul_assoc ..).symm
  unfold replica; split
  · rwa [G.chord_one]
  exact hV _
end transition

section all
variable {d : Descent n c} {t : d.Tags} {x : Fields G d} {r w : ℝ} {V : Config G c}
    (hr : 0 ≤ r) (hp : 0 < d.probability t x) (he : d.action t V x ≤ r^2)

private lemma top_face (V : Config G n) {r : ℝ} (hr : 0 ≤ r) (he : energy V ≤ r^2) :
    QuietFaces V (Real.sqrt 2 * r) := by
  intro j
  apply (sq_le_sq₀ (G.chord_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)).mp
  have h : G.price (faceValue V j) ≤ energy V := Finset.single_le_sum (f := fun p => G.price (faceValue V p))
    (fun p _ => (G.price_range _).1) (Finset.mem_univ _)
  rw [G.chord_price, mul_pow, Real.sq_sqrt (by norm_num)]; linarith

@[simp] lemma action_push (S : StepData c f) (T : Forest S.ratio) (D : Descent n f) (V : Config G c)
    (t : (push S T D).Tags) (x : Fields G (push S T D)) : (push S T D).action t V x =
      tagEnergy S t.1 (T.drape (x ∘ Sum.inl)) V + D.action t.2 (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr) := by
  rw [action,account, Pi.one_apply, one_mul]; rfl

include hr hp he
lemma controls_faces : QuietFaces V (d.faceBill G*r) := by
  induction d with
  | nil =>
    apply top_face V hr
    simpa only [action, account, Pi.one_apply, one_mul] using he
  | @push m i S T d ih =>
    have ht := (action_nonneg d t.2 (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr))
    have hz : 0 ≤ tagEnergy S t.1 (T.drape (x ∘ Sum.inl)) V := (energy_estimate S _).nonneg V
    rw [probability] at hp; rw [action_push] at he
    rw [faceBill, add_mul, mul_assoc (faceUnit G _ _)]
    apply downward S (t := t.1) (U := T.drape (x ∘ Sum.inl)) hr
    · exact (le_add_of_nonneg_right ht).trans he
    · exact pos_of_mul_pos_left hp (probability_nonneg d t.2 _)
    exact ih (pos_of_mul_pos_right hp (S.likelihood_pos ..)) ((le_add_of_nonneg_left hz).trans he)

lemma controls_links (h : d.Room G) (hv : QuietLinks V w) (hw : 0 ≤ w) (j : d.Links) :
    G.chord (x j) ≤ d.edgeBill G*r + w := by
  induction d generalizing w with
  | nil => exact Empty.elim (by exact j)
  | @push m i S T d ih =>
    have ht := action_nonneg d t.2 (T.drape (x ∘ Sum.inl)) (x ∘ Sum.inr)
    have hz : 0 ≤ tagEnergy S t.1 (T.drape (x ∘ Sum.inl)) V := (energy_estimate S _).nonneg V
    rw [probability] at hp; rw [action_push] at he
    have hp' := pos_of_mul_pos_right hp (S.likelihood_pos ..)
    have hb := (le_add_of_nonneg_left hz).trans he
    have hh := controls_faces hr hp' hb
    let p := edgeUnit G S.kernel S.patch * (d.faceBill G * r) + noiseUnit S.kernel * r + w
    have hy : QuietLinks (T.drape (x ∘ Sum.inl)) p := upward S hr ((le_add_of_nonneg_right ht).trans he) h.1 T
      (fun i hi => T.on_tree _ ⟨i,hi⟩) (pos_of_mul_pos_left hp (probability_nonneg d ..)) hh hv hw
    have hP : 0 ≤ p := add_nonneg (add_nonneg
      (mul_nonneg (edgeUnit_nonneg ..) (mul_nonneg (faceBill_nonneg G d) hr))
      (mul_nonneg (Real.sqrt_nonneg _) hr)) hw
    rw [show (push S T d).edgeBill G*r + w = d.edgeBill G*r + p by unfold p; rw [edgeBill]; ring]
    change T.Free ⊕ d.Links at j
    cases j with
    | inl j =>
      have hy := hy j.val
      rw [T.off_tree (x ∘ Sum.inl) j] at hy
      exact hy.trans (le_add_of_nonneg_left (mul_nonneg (edgeBill_nonneg ..) hr))
    | inr j => exact ih hp' hb h.2 hy hP j

omit hr hp he

/-- The action at coarsest 1 is a genuine isolated minimum in the joint integrated coordinates
(in a likelihood-positive branch). Quantitative per-link bound -- all tags, all configurations on
the slice path. Reusable by tail and Gaussian comparisons. -/
theorem from_flat (h : d.Room G) (hp : 0 < d.probability t x) (j : d.Links) :
    G.chord (x j) ≤ d.edgeBill G * Real.sqrt (d.action t 1 x) := by
  simpa using controls_links (Real.sqrt_nonneg _) hp (V := (1 : Config G c))
    (Real.sq_sqrt (action_nonneg ..)).symm.le h (w := 0) (fun i => G.chord_one.le) le_rfl j
end all
end YM.RGComparison.Core16.Descent
