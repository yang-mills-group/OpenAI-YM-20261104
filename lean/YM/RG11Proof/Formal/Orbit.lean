import YM.RG11Proof.Formal.Ruler

/-!
# Formal quotient by frames and coupling at one field horizon

The change with zero detector prices exists and is unique (including tangent).
With the indicated first-order nonvanishing response, it is a formal group
change. Solving prices only does *not* imply physical or even off-diagnostic
matching; we exhibit their simultaneous vanishing by diagnostic-centered differences (every slot,
not just the detector); actual normal form in Normal.lean. Theorems here give a formal quotient criterion via deflected (diagnostic-centered difference) arrays in finite
jets with naturality under precomposition by already allowed frames/couplings.
Regulator estimates to prove equality on this quotient are another obligation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Formal
open PowerSeries YM.RG11.Jets YM.PertExtension.Position
open scoped BigOperators Classical
variable {R J P : Type*} [Field R] [Fintype J] [DecidableEq J] {shape : P→ℕ}
variable {L : Constraints R J} {A B : ArrayAt J R shape}

def ArrayThrough (n : ℕ) {P} {shape : P → ℕ} (A B : ArrayAt J R shape) := ∀ v, Through n (A v) (B v)
namespace ArrayThrough
variable {n m : ℕ} {C : ArrayAt J R shape}
omit [Fintype J] [DecidableEq J] in
protected theorem refl : ArrayThrough n A A := fun _=> Through.refl _
omit [Fintype J] [DecidableEq J] in
protected theorem symm (h : ArrayThrough n A B) : ArrayThrough n B A := fun v=> (h v).symm
omit [Fintype J] [DecidableEq J] in
protected theorem trans (h : ArrayThrough n A B) (hp : ArrayThrough n B C) : ArrayThrough n A C := fun v=> (h v).trans (hp v)
omit [Fintype J] [DecidableEq J] in
protected theorem of_le (h : ArrayThrough n A B) (hm : m≤n) : ArrayThrough m A B := fun v=> Through.of_le hm (h v)
omit [DecidableEq J] in
theorem act (h : ArrayThrough n A B) {c d : Change R J} (hc : Anchored c.g) (hp : c.EquivJet d n) :
    ArrayThrough n (c.act A) (d.act B) := fun v=> hp.act hc (fun _=> h _) (v:=v)
end ArrayThrough

def Converted (L : Constraints R J) (n : ℕ) (A B : ArrayAt J R shape) :=
  ∃ c : Change R J, Change.Good L c ∧ ArrayThrough n B (c.act A)
namespace Converted
variable {n m : ℕ} {C : ArrayAt J R shape}
@[refl] theorem refl (n) (L : Constraints R J) (A : ArrayAt J R shape) : Converted L n A A :=
  ⟨Change.one R J,Change.Good.id _, by rw [Change.act_one]; exact ArrayThrough.refl⟩
@[symm] theorem symm (h : Converted L n A B) : Converted L n B A := by
  obtain ⟨c,h,H⟩ := h
  exact ⟨c.undo h, Change.Good.undoes c h, Change.match_reverse c h (fun v=> (H v).symm)⟩

theorem trans (h : Converted L n A B) (h' : Converted L n B C) : Converted L n A C := by
  obtain ⟨c,G,H⟩ := h
  obtain ⟨d,G',H'⟩ := h'
  refine ⟨Change.compose d c,G'.compose G,?_⟩
  rw [← Change.act_act d c G'.ruler.base G.ruler.base]
  exact H'.trans (H.act G'.ruler.base Change.EquivJet.refl)
end Converted

omit [DecidableEq J] in
theorem hits_of_through (D : Detector L A) {c} {n} (he : ArrayThrough n B (c.act A)) {m}
    (hm : m ≤ n) : Hits D B c m :=
  congrArg D.restore (funext fun i=> he (D.test i) m hm)

/-- A match in ALL tested arrays through desired order gives the calibration
solution there. Requires only Law (not invertibility of the formal ruler),
no higher order alignment. -/
theorem identification (D : Detector L A) {c} (hc : Law L c) {n}
    (he : ArrayThrough n B (c.act A)) : c.EquivJet (solution D B) n :=
  uniqueness D B hc (solution_law D B) n (fun _ hm _=> hits_of_through D he hm) (fun _ _ hi=> hits D B hi)

/-- Defect left after solving the detector, still in B's ruler and columns
(coefficient equality of these zero defects includes the zeroth-order identity,
NOT something D would force at n=0). -/
def defect (D : Detector L A) (B : ArrayAt J R shape) : ArrayAt J R shape :=
    B - (solution D B).act A

theorem detector_centered (D : Detector L A) (B : ArrayAt J R shape) {n} (hn:0<n) :
    price D (defect D B) n = 0 := by
  unfold price defect; simp_rw [Pi.sub_apply,map_sub]
  rw [show (fun i=> coeff n (B (D.test i)) - _) =
    (fun i=> coeff n (B (D.test i))) - (fun i=>coeff n ((solution D B).act A (D.test i))) from rfl]
  rw [map_sub]
  exact sub_eq_zero.mpr (hits D B hn)

theorem defect_zero_of_convert (D : Detector L A) {n : ℕ} (h : Converted L n A B) :
    ArrayThrough n (defect D B) 0 := by
  obtain ⟨c,h,H⟩ := h
  have hh := identification D ⟨h.ruler.base,h.field⟩ H
  have hw : ArrayThrough n B ((solution D B).act A) := H.trans
    ((ArrayThrough.refl (A:=A)).act h.ruler.base hh)
  intro v i hi
  change coeff i (_-_) = coeff i (0:R⟦X⟧)
  rw [map_sub,hw v i hi,map_zero,sub_self]

theorem convert_of_defect_zero (D : Detector L A) {n} (hg : Change.Good L (solution D B))
    (h : ArrayThrough n (defect D B) 0) : Converted L n A B := by
  refine ⟨solution D B,hg,?_⟩
  intro v i hi; apply sub_eq_zero.mp; rw [← map_sub]
  exact Eq.trans (h v i hi) ((coeff i).map_zero)

-- The coherence of solving calibration under finite truncation of the B
-- or A arrays. Other detectors with unrelated choices are not identified
-- without further matching (a normalization must be pinned).
theorem solution_coherent (D : Detector L A) {A' B' : ArrayAt J R shape} {n}
    (ha : ArrayThrough n A A') (ha' : ArrayThrough 1 A A')
    (hb : ArrayThrough n B B') :
    (solution D B).EquivJet (solution (D.ofFirst ha') B') n := by
  let Q := D.ofFirst ha'
  let c:= solution D B
  let d:= solution Q B'
  have hc : Law L c:=solution_law D B
  apply uniqueness Q B' hc (solution_law Q B') n
  · intro i hi hp
    have H := hits D B hp
    have he : ArrayThrough n (c.act A) (c.act A') := ha.act hc.1 Change.EquivJet.refl
    have hB v := hb v i hi
    have hV v := he v i hi
    unfold price Hits at H -- Hits abbrev? unfold order fix
    change D.restore (fun m=>coeff i (B' (D.test m)))=D.restore (fun m=>coeff i (c.act A' (D.test m)))
    simp_rw [← hB, ← hV]; exact H
  intro i hi hp; exact hits Q B' hp

/-! For a canonical normal form, rather than attempt equivariance of the
vanishing *defect* itself on the unmatched jets, perform the detector-solve
between the two arrays being compared (D on whichever will be inserted).
If any allowed frame change exists, it must be selected by the detector. -/
theorem price_quotient (T : RulerTest L A) (h : Free L A) {n} (hb : T.priceAt B 1≠0) :
    let D := T.pin (Detector.ofSees (Sees.of_parts h T))
    Converted L n A B ↔ ArrayThrough n (defect D B) 0 := by
  intro D
  exact ⟨defect_zero_of_convert D, convert_of_defect_zero D (T.calibrate_good h hb)⟩

-- Naturality for aligned arrays in finite precision and a fixed field law.
theorem recalibrated {c : Change R J} (D : Detector L A) (hg : Change.Good L c) {n}
    (h : ArrayThrough n B ((solution D B).act A)) (hs : Change.Good L (solution D B)) :
    (Change.compose c (solution D B)).EquivJet (solution D (c.act B)) n := by
  have hw := h.act hg.ruler.base Change.EquivJet.refl
  have he := Change.act_act c (solution D B) hg.ruler.base hs.ruler.base A
  refine identification D ⟨(hg.compose hs).ruler.base,(hg.compose hs).field⟩ ?_
  rw [← he]; exact hw
end YM.RG11.Formal
