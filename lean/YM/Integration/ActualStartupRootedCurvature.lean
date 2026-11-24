import YM.Integration.ActualStartupCurvaturePackets
import YM.Work.F03.Transport

/-!
The original signed startup rows at their stored roots. The connector uses
only the negative directions needed to reach the positive plaquette base.
All original labels remain unchanged; zero-padding compatibility is separate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupRootedCurvature

open Function Finset Lattice Wilson RG Tensor
open WilsonStartup WilsonStartup.Start WilsonStartup.IterationFour
open ActualStartupCurvaturePackets
open scoped Classical BigOperators Matrix.Norms.Frobenius

attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n : Side} {k : ℕ}

def lowerWalk (a b : Step) : Walk :=
  (if a.neg then [a] else []) ++ (if b.neg then [b] else [])

def connector (s : Signed) (b : PlaqAxes) : Slot :=
  ⟨lowerWalk ((posDir b.val.1).rotate s) ((posDir b.val.2).rotate s),
    b.rotate s⟩

private theorem lowerWalk_length (a b : Step) : (lowerWalk a b).length ≤ 2 := by
  cases ha : a.neg <;> cases hb : b.neg <;> simp [lowerWalk, ha, hb]

private theorem lowerWalk_stop {A : Type*} [AddCommGroup A] [One A]
    (a b : Step) (x : Four A) : stop x (lowerWalk a b) = atFace x a b := by
  cases ha : a.neg <;> cases hb : b.neg <;>
    simp [lowerWalk, atFace, ha, hb, stop]

private theorem oriented_corners {A : Type*} [AddCommGroup A] [One A] [DecidableEq A]
    (a b : Step) (x : Four A) :
    (visits x (oriented a b)).toFinset =
      {x, x + a.vec, x + b.vec, x + a.vec + b.vec} := by
  simp only [visits, oriented, Step.vec_rev,
    show x + a.vec + b.vec + -a.vec = x + b.vec by abel, add_neg_cancel_right]
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset,
    List.mem_cons, List.not_mem_nil]
  tauto

private theorem lowerWalk_visits {A : Type*} [AddCommGroup A] [One A] [DecidableEq A]
    (a b : Step) (x : Four A) :
    (visits x (lowerWalk a b)).toFinset ⊆ (visits x (oriented a b)).toFinset := by
  rw [oriented_corners]
  intro y hy
  cases ha : a.neg <;> cases hb : b.neg <;>
    simp [lowerWalk, ha, hb, visits] at * <;> tauto

private theorem visits_wrap (x : Cover) (o : Site n) (w : Walk) :
    (visits x w).map (fun y => wrap n y + o) = visits (wrap n x + o) w := by
  induction w generalizing x with
  | nil => simp [visits]
  | cons d w ih =>
      simp only [visits, List.map_cons, ih, map_add, wrap_vec]
      rw [add_right_comm (wrap n x) (d.vec : Site n) o]

private theorem visits_affine (s : Signed) (t x : Site n) (w : Walk) :
    (visits x w).map (affine s t) =
      visits (affine s t x) (w.map (·.rotate s)) := by
  induction w generalizing x with
  | nil => simp [visits]
  | cons d w ih =>
      simp only [visits, List.map_cons, ih, Step.vec_rotate]
      rw [show affine s t (x + d.vec) = affine s t x + s.act d.vec by
        rw [affine, affine, Signed.act_add]; abel]

/-- The original base is shifted by at most two actual coordinate steps. -/
theorem connector_length (s : Signed) (b : PlaqAxes) :
    (connector s b).length ≤ 6 := by
  have h := lowerWalk_length ((posDir b.val.1).rotate s) ((posDir b.val.2).rotate s)
  change (lowerWalk _ _).length + 4 ≤ 6
  omega

/-- The connected square is exactly the original signed row's positive face. -/
theorem connector_face (i : Key n) :
    Work.F03.slotFace (connector i.1 i.2.2) i.native = i.positive := by
  apply Prod.ext
  · change wrap n (stop 0 (lowerWalk _ _)) + i.native =
      atFace (affine i.1 i.native 0) _ _
    rw [wrap_stop_cover]
    simp only [map_zero, lowerWalk_stop, atFace, affine, Signed.act_zero, zero_add, Key.root]
    abel
  · rfl

private theorem key_oriented_sites (i : Key n) :
    (visits i.native (oriented ((posDir i.2.2.val.1).rotate i.1)
      ((posDir i.2.2.val.2).rotate i.1))).toFinset = i.skin := by
  have h := visits_affine i.1 i.native (0 : Site n)
    (square i.2.2.val.1 i.2.2.val.2)
  have hw : (square i.2.2.val.1 i.2.2.val.2).map (·.rotate i.1) =
      oriented ((posDir i.2.2.val.1).rotate i.1)
        ((posDir i.2.2.val.2).rotate i.1) := by
    change (oriented (posDir _) (posDir _)).map _ = _
    simp [oriented, ← Step.rev_rotate]
  rw [hw] at h
  have hm (xs : List (Site n)) :
      (xs.map (affine i.1 i.native)).toFinset =
        xs.toFinset.image (affine i.1 i.native) := by
    ext y
    simp
  have hs := congrArg List.toFinset h
  rw [hm] at hs
  simpa [Key.skin, Key.root, touched, affine] using hs.symm

/-- Every connector and square vertex stays inside the original row support. -/
theorem connector_support (i : Key n) :
    (connector i.1 i.2.2).stencil.image (fun z => wrap n z + i.native) ⊆ i.skin := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rcases Finset.mem_union.mp hz with hz | hz
  · have hm : wrap n z + i.native ∈
        (visits 0 (connector i.1 i.2.2).walk).map
          (fun q => wrap n q + i.native) :=
      List.mem_map.mpr ⟨z, List.mem_toFinset.mp hz, rfl⟩
    rw [visits_wrap] at hm
    simp only [map_zero, zero_add] at hm
    change wrap n z + i.native ∈ visits i.native
      (lowerWalk ((posDir i.2.2.val.1).rotate i.1)
        ((posDir i.2.2.val.2).rotate i.1)) at hm
    have hs := lowerWalk_visits (A := Per n)
      ((posDir i.2.2.val.1).rotate i.1)
      ((posDir i.2.2.val.2).rotate i.1) i.native
    have ho := hs (List.mem_toFinset.mpr hm)
    rw [key_oriented_sites i] at ho
    exact ho
  · have hm : wrap n z + i.native ∈
        (visits (connector i.1 i.2.2).offset
          (square (connector i.1 i.2.2).plaq.val.1
            (connector i.1 i.2.2).plaq.val.2)).map
          (fun q => wrap n q + i.native) :=
      List.mem_map.mpr ⟨z, List.mem_toFinset.mp hz, rfl⟩
    rw [visits_wrap] at hm
    have ht : wrap n z + i.native ∈ touched
        (Work.F03.slotFace (connector i.1 i.2.2) i.native) :=
      List.mem_toFinset.mpr hm
    rw [connector_face, ← i.skin_positive] at ht
    exact ht

def rootedAtom (G : Gauge) (u : ℝ) (s : Slot) (k : ℕ) : Atom G k where
  leg := fun _ => s
  coeff := (atom G u s.plaq k).coeff

private theorem rooted_poly (u : ℝ) (s : Slot) (k : ℕ) (x : Fin k → G.Color) :
    (rootedAtom G u s k).poly x = (u • coeff (inK G) k 0) x :=
  Design.extract_poly s.plaq _ x

theorem rooted_invariant (u : ℝ) (s : Slot) (k : ℕ) :
    (rootedAtom G u s k).Invariant :=
  atom_invariant u s.plaq k

/-- Connector holonomy disappears by the actual tensor's adjoint invariance. -/
theorem rooted_unmasked (u : ℝ) (s : Slot) (k : ℕ)
    (o : Site n) (U : Config G n) :
    (rootedAtom G u s k).unmasked U o =
      u * element G (terms G k) (Work.F03.slotFace s o) U := by
  unfold Atom.unmasked
  rw [rooted_poly]
  simp only [rootedAtom, Work.F03.atSite_path]
  change u * coeff (inK G) k 0 (fun _ => G.adjoint (travel U o s.walk)
      (G.curvature (faceValue U (Work.F03.slotFace s o)))) =
    u * coeff (inK G) k 0
      (fun _ => Quad.kMat (G.mat (faceValue U (Work.F03.slotFace s o))))
  rw [coeff_adjoint, Quad.k_actual]

theorem rooted_length (u : ℝ) (s : Slot) (k : ℕ) :
    (rootedAtom G u s k).length = k * s.length := by
  simp [Atom.length, rootedAtom]

theorem rooted_magnitude (u : ℝ) (s : Slot) (k : ℕ) :
    (rootedAtom G u s k).magnitude = |u| * coefficientCost G k :=
  atom_magnitude u s.plaq k

/-- Uniform finite cost keeps the actual connector lengths before bounding them. -/
theorem rooted_connector_budget (u width : ℝ) (hwidth : 0 ≤ width)
    (i : Key n) (k : ℕ) :
    (rootedAtom G u (connector i.1 i.2.2) k).budget width ≤
      |u| * coefficientCost G k * Real.exp (width * (k * 6 : ℕ)) := by
  rw [Atom.budget, rooted_magnitude, rooted_length]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (coefficientCost_nonnegative G k))
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hwidth
  exact_mod_cast Nat.mul_le_mul_left k (connector_length i.1 i.2.2)

/-- The same original padded row, now evaluated at its stored native root. -/
theorem slate_rooted_action (u : ℝ) (k : ℕ) (i : Key n) (U : Config G n) :
    (slate G n u (terms G k)).action
        (Padded.index (Sum.inl i : Sheet n)) U =
      (rootedAtom G u (connector i.1 i.2.2) k).unmasked U i.native := by
  rw [rooted_unmasked, connector_face]
  simp [slate]

/-- The actual atom lies in the original stored support, without relabeling. -/
theorem rooted_support (u : ℝ) (k : ℕ) (i : Key n) :
    (rootedAtom G u (connector i.1 i.2.2) k).footprint i.native ⊆ i.skin := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    simpa using i.native_mem
  · obtain ⟨j, _, hz⟩ := Finset.mem_biUnion.mp hz
    exact connector_support i (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

end YM.Integration.ActualStartupRootedCurvature
end
