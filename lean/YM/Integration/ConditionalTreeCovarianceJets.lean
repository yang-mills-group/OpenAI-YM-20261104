import YM.Push.FREE_RESOLVENT.Costed
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Greenbelt

/-! Flat jets of the completed no-hole affine precision. A physical tree draw
is held on every block except the one actually changed. The extra interpolation
slot retains that block alongside every independently placed coarse field slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalTreeCovarianceJets
open Lattice Wilson RG Precision Tree Matrix FreeResolvent FreeResolvent.Affine
  FreeResolvent.Mark FreeResolvent.TestD FreeResolvent.Lever PhysicalNext.Repeat.Greenbelt
  Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- A bond in the assembled forest reads its original tree draw at the
parent of its origin, also when the oriented tree step is negative. -/
theorem allot_trunks (r s : Reserve S) (i : Edge (Site f))
    (hi : r (S.ratio.parent i.1) = s (S.ratio.parent i.1)) :
    i ∈ (allot r).trunks ↔ i ∈ (allot s).trunks := by
  suffices H : ∀ r s : Reserve S, r (S.ratio.parent i.1) = s (S.ratio.parent i.1) →
      i ∈ (allot r).trunks → i ∈ (allot s).trunks from ⟨H _ _ hi,H _ _ hi.symm⟩
  intro r s he h
  obtain ⟨j,hj,hb⟩ := ((allot r).trunk_mem_iff _).mp h
  have hp : S.ratio.parent i.1 = S.ratio.parent j := by
    let d := (allot r).up j
    have h₁ := (allot r).stays j hj
    change S.ratio.parent (j+d.vec) = _ at h₁
    change d.used j = i at hb
    rw [←hb]
    cases hd : d with
    | mk k b =>
      rw [hd] at h₁
      cases b <;> simp only [Step.used,Bool.false_eq_true,↓reduceIte,Step.vec,←sub_eq_add_neg] at h₁ ⊢
      exact h₁
  rw [hp] at he
  refine ((allot s).trunk_mem_iff _).mpr ⟨j,hj,?_⟩
  simpa only [allot,he] using hb

theorem change_draw (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w) :
    changed S (allot r) (allot s) v := fun i hi => allot_trunks r s i (h _ hi)

variable {t : S.Choices} {p : Clip} {W : PathData G} {σ A u : ℝ} {n : ℕ}
  (hs : 0 < σ) (ha : 0 ≤ A) (hW : Sheet W σ A) (he : Bid.Larger (G:=G) S) (hu : 0 ≤ u)

def windowError {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (Z : FreeResolvent.Window.Survey I) (T : Forest S.ratio) (t : S.Choices)
    (p : Clip) (W : PathData G) (q : Admit) (u : ℝ) :=
  glimpse Z (whole S T t p W q) u - action (whole S T t p W q) u

def windowPrice (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ)
    (A σ u R : ℝ) :=
  patchFee (width G P K p n A σ) R (nuts G P K p n A σ) 1
    (locker G P K p n A σ) (earnings G P K p n A σ * drain u) n

include hs ha hW he hu

private theorem window_family {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    {R : ℝ} (Z : FreeResolvent.Window.Survey I) (hZ : Z.Near (native c) (home S) R)
    {T U : Forest S.ratio} {v : Site c} (hTU : changed S T U v) (q : Admit)
    {θ : ℝ} (hθ : θ ∈ Icc (0:ℝ) 1) :
    let d := width G S.patch S.kernel p n A σ
    let F := crest S t (W:=W) (T:=T) (U:=U) (p:=p) q
    Bundle (guides (ray G c)) (park (native c) hearth d v) (native c) (home S) (home S)
      (glimpse Z F u - action F u) (0,θ) n d (windowPrice G S.patch S.kernel p n A σ u R) := by
  intro d F
  have hP := gauged G S.patch S.kernel p n hs ha
  exact (mast S t hs ha hW he hTU q hθ).discrepancy hP hu
    (position_move _ _ hP.pos.le) (home_volume S 1 _ hP.pos) hZ

/-- Finite difference of the physical window error with the changed block
and all derivative positions retained. Both spectral resolvents enter the
price, making it integrable in their common shift. -/
theorem window_tag {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    {R : ℝ} (Z : FreeResolvent.Window.Survey I) (hZ : Z.Near (native c) (home S) R)
    (r s : Reserve S) (v : Site c) (h : ∀ w, w ≠ v → r w = s w)
    (q : Admit) (l : List (raw G c)) (hl : l.length < n) :
    let d := width G S.patch S.kernel p n A σ
    Here (ray G c) (native c) (home S) hearth d d v l (windowPrice G S.patch S.kernel p n A σ u R)
      (windowError Z (allot r) t p W q u) (windowError Z (allot s) t p W q u) := by
  intro d
  let Zθ := crest S t (W:=W) (T:=allot r) (U:=allot s) (p:=p) q
  refine paid (G:=glimpse Z Zθ u - TestD.action Zθ u) ?_ ?_ hl ?_
  · intro x
    exact congrArg (fun Q => Z.inspect Q u - resolve Q u) (now (allot r) (allot s) t p q x)
  · intro x
    exact congrArg (fun Q => Z.inspect Q u - resolve Q u) (thenAt (allot r) (allot s) t p q x)
  exact fun θ hθ => window_family hs ha hW he hu Z hZ (change_draw r s v h) q hθ

/-- The undifferenced window error at the exact same flat background. -/
theorem window_regular {I : raw G f → Type*} [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    {R : ℝ} (Z : FreeResolvent.Window.Survey I) (hZ : Z.Near (native c) (home S) R)
    (r : Reserve S) (v : Site c) (q : Admit) :
    let d := width G S.patch S.kernel p n A σ
    Bundle (ray G c) (positions (native c) hearth d) (native c) (home S) (home S)
      (windowError Z (allot r) t p W q u) 0 n d (windowPrice G S.patch S.kernel p n A σ u R) := by
  intro d
  have hf := window_family hs ha hW he hu (t:=t) (p:=p) (n:=n) Z hZ
    (change_draw r r v (fun _ _ => rfl)) q (Set.left_mem_Icc.mpr zero_le_one)
  refine (restricted 0 hf).glue (Eventually.of_forall fun x => ?_)
  exact congrArg (fun Q => Z.inspect Q u - resolve Q u) (now (allot r) (allot r) t p q x)

end YM.Integration.ConditionalTreeCovarianceJets
