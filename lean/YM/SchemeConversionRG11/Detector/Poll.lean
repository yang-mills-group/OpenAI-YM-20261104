import YM.SchemeConversionRG11.Field.Restriction

/-!
# Nested finite menus of determining separated tests

Coordinates correspond to the ACTUAL free quotient and signed symmetry at all horizons.
Provided the free infinitesimal rank test (`Frozen`), make square tests as in
`Pert.Position.Detect` but cohere across higher and derivative horizons.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Detector

open Function Filter Horizon Pert.Position Maxwell
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G}
variable {d e : ℕ}

/-- Finite list of positions/profiles yielding a return coordinate. -/
structure Poll (F : Labels.Frames G) (d : ℕ) where
  tests : ℕ
  table : Fin tests → Section F d
  pointer : (Fin tests → ℝ) →ₗ[ℝ] Buffer F d
  checks (B : Buffer F d) : pointer (fun i ↦ feedback F d (table i) B) = B

namespace Poll

/-- Convert this poll to a position Scheme Board (no determining-data change). -/
noncomputable def num (F : Labels.Frames G) (d : ℕ) := Module.finrank ℝ (Buffer F d)

noncomputable def numbering (F : Labels.Frames G) (d : ℕ) : Buffer F d ≃L[ℝ] (Fin (num F d) → ℝ) := by
  letI hfree : Module.Free ℝ (Buffer F d) := @Module.Free.of_divisionRing ℝ (Buffer F d) _ _ _
  let B : Buffer F d ≃ₗ[ℝ] (Fin (num F d) → ℝ) := (Module.finBasis ℝ (Buffer F d)).equivFun
  exact LinearEquiv.toContinuousLinearEquiv (𝕜:=ℝ) (E:=Buffer F d) (F:=Fin _ → ℝ) B

def board (Q : Poll F d) : Conditions F d (num F d) :=
  assemble F d Q.table (num F d) (LinearMap.comp (numbering F d).toLinearMap Q.pointer)

/-- Explicit square under the existing API, derivative at the **free** measured array. -/
theorem measured (Q : Poll F d) : square Q.board := by
  refine ⟨numbering F d, ?_⟩; ext1 B
  change numbering F d B = fderiv ℝ (chart Q.board) (white Q.board,0) (0,B)
  rw [board, chart_deriv_formula, LinearMap.comp_apply, Q.checks]; rfl

theorem clean {C : Family G} (Q : Poll C.labels d) : CleanProfiles (C := C) Q.board := by
  -- The C form is only used for actual data; see bridge file for adapter
  intro i; exact ⟨(Q.table i).f, rfl⟩

/-- Include a lower-horizon section, with the VERY SAME test and shape. -/
def grow (h : d ≤ e) (u : Section F d) : Section F e :=
  ⟨u.r, fun i ↦ incl F h (u.p i), u.f⟩

lemma visibleIncl {r : ℕ} (p : Fin r → E F d) (x : Points r) (h : d ≤ e) :
    visible F e x (fun j ↦ incl F h (p j)) = visible F d x p := by
  change (freeTable F).useAt (freeTable F) x (fun j ↦ ⟨e,incl F h (p j)⟩) =
    (freeTable F).useAt (freeTable F) x (fun j ↦ ⟨d,p j⟩)
  rw [Free.display F, Free.display F]
  congr 1
  funext j
  exact Free.address_rise F _ h (p j)

theorem feedback_inc (h : d ≤ e) (u : Section F d) (B : Buffer F e) :
    feedback F e (grow h u) B = feedback F d u (restr F h B) := by
  rw [current_read, current_read]
  have he : current F e (grow h u) B = current F d u (restr F h B) := by
    funext x; dsimp only [grow, current]; apply Finset.sum_congr rfl
    intro i _
    let w := Function.update u.p i ((restr F h B).val (u.p i))
    change visible F e x (Function.update (fun j ↦ incl F h (u.p j)) i (B.val _)) = visible F d x w
    have he : Function.update (fun j ↦ incl F h (u.p j)) i (B.val (incl F h (u.p i))) =
        fun j : Fin u.r ↦ incl F h (w j) := by
      funext j
      by_cases t : j=i
      · subst j
        simp only [w, Function.update_self, restrictions]
      simp only [w, Function.update_of_ne t]
    exact (congrArg (fun v : Fin u.r → E F e ↦ visible F e (show Points u.r from x) v) he).trans
      (visibleIncl w x h)
  rw [he]; rfl

/-- Nested normalization: the higher equations impose the SAME previous tests. -/
def Carries (p : Poll F d) (q : Poll F e) (h : d ≤ e) :=
  ∀ (a : Section F e → ℝ), restr F h (q.pointer (fun i ↦ a (q.table i))) =
    p.pointer (fun i ↦ a (grow h (p.table i)))

theorem exists_test (h : Frozen F d) : Nonempty (Poll F d) := by
  obtain ⟨k,s,hs⟩ := finite_detectors F d h
  let f := LinearMap.pi (fun i : Fin k ↦ feedback F d (s i))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (K:=ℝ) (V:=Buffer F d) (V':=Fin k→ℝ) f hs
  exact ⟨⟨k,s,g, fun B ↦ LinearMap.congr_fun hg B⟩⟩

/-- Extend p at a larger horizon (also works at the same). The numerical derivatives are
  computed separately at each horizon's *free* system, not the rotated arrays. -/
theorem extends_test (u : Frozen F e) (p : Poll F d) (h : d ≤ e) :
    ∃ q : Poll F e, p.Carries q h := by
  obtain ⟨q⟩ := exists_test u
  let R : Buffer F e →ₗ[ℝ] Buffer F d := (restr F h).toLinearMap
  letI hfree : Module.Free ℝ (Buffer F d) := @Module.Free.of_divisionRing ℝ (Buffer F d) _ _ _
  obtain ⟨L, hL⟩ := LinearMap.exists_rightInverse_of_surjective (R := ℝ) (M := Buffer F e)
    (P := Buffer F d) R (LinearMap.range_eq_top.mpr (restr_surjective F h))
  let T := p.tests + q.tests
  let low (v : Fin T → ℝ) (i : Fin p.tests) := v (Fin.castAdd q.tests i)
  let high (v : Fin T → ℝ) (i : Fin q.tests) := v (Fin.natAdd p.tests i)
  let lmap : (Fin T → ℝ) →ₗ[ℝ] Buffer F d := p.pointer.comp
    ({ toFun := low, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } : (Fin T → ℝ) →ₗ[ℝ] (Fin p.tests → ℝ))
  let hmap : (Fin T → ℝ) →ₗ[ℝ] Buffer F e := q.pointer.comp
    ({ toFun := high, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } : (Fin T → ℝ) →ₗ[ℝ] (Fin q.tests → ℝ))
  let pre : (Fin T → ℝ) →ₗ[ℝ] Buffer F e := {
    toFun w := hmap w + L (lmap w - R (hmap w))
    map_add' a b := by
      simp only [map_add]
      rw [show lmap a + lmap b - (R (hmap a) + R (hmap b)) = (lmap a - R (hmap a)) + (lmap b - R (hmap b)) from add_sub_add_comm (lmap a) (lmap b) (R (hmap a)) (R (hmap b)), map_add]
      exact add_add_add_comm (hmap a) (hmap b) (L (lmap a - R (hmap a))) (L (lmap b - R (hmap b)))
    map_smul' c a := by
      simp only [map_smul]; rw [show c • lmap a - c • R (hmap a) = c • (lmap a - R (hmap a)) from (smul_sub c (lmap a) (R (hmap a))).symm, map_smul]; exact (smul_add c (hmap a) (L (lmap a - R (hmap a)))).symm }
  let t : Fin T → Section F e := Fin.append (fun i ↦ grow h (p.table i)) q.table
  have t₁ (i) : t (Fin.castAdd q.tests i) = grow h (p.table i) := Fin.append_left ..
  have t₂ (i) : t (Fin.natAdd p.tests i) = q.table i := Fin.append_right ..
  have hop (B : Buffer F e) : pre (fun i ↦ feedback F e (t i) B) = B := by
    let w (i : Fin T) := feedback F e (t i) B
    have H : hmap w = B := by
      change q.pointer (high w) = B; simp only [high,w,t₂]; exact q.checks B
    have K : lmap w = R B := by
      change p.pointer (low w) = R B; simp only [low,w,t₁,feedback_inc]; exact p.checks (R B)
    change hmap w + L (lmap w - R (hmap w)) = B
    rw [H,K, show R B - R B=0 from sub_self (R B),map_zero, add_zero]
  refine ⟨⟨T, t, pre, hop⟩, fun a ↦ ?_⟩
  let w (i : Fin T) := a (t i)
  have he : lmap w = p.pointer (fun i ↦ a (grow h (p.table i))) := by
    change p.pointer (low w) = _; simp only [low,w,t₁]
  change R (hmap w + L (lmap w - R (hmap w))) = _
  have hc (v : Buffer F d) : R (L v) = v := LinearMap.congr_fun hL v
  rw [← he, map_add, hc]; abel

theorem sequence (H : ∀ d, Frozen F d) : ∃ c : (d : ℕ) → Poll F d,
    ∀ i, (c i).Carries (c (i+1)) (Nat.le_succ i) := by
  let p := Classical.choice (exists_test (H 0))
  let c (i : ℕ) : Poll F i := Nat.rec p (fun i p ↦ Classical.choose (p.extends_test (H (i+1)) (Nat.le_succ i))) i
  exact ⟨c, fun i ↦ Classical.choose_spec ((c i).extends_test (H (i+1)) (Nat.le_succ i))⟩
end Poll
end YM.SchemeConversionRG11.Detector
