import YM.WilsonMS.Top.TreeAnswer
import YM.MS.Swirl.Migrate

/-!
# The actual finite Fourier transform for `PhysicalSum`

Used for *every* rank. Do not include a volume per fixed (position) source;
`Bulk` already counts correctly for the unmarked exponent. Also `run` by
itself wouldn't agree as it has a half-link offset phase.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open XSpace Lattice Function Filter Set Finset
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Native
open MS.Book MS.Book.Convolve MS.Swirl MS.Orbit MS.Orbit.Cog
open MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom MS.Fleet
open MS.Plane MS.Landau MS.Tone MS.Swirl.Near Bloch
open Matrix
open scoped Topology BigOperators

variable (G : Gauge) {n : Side} (N : Side)

def fourier (n : Side) : Matrix (FixedMode G n) (FixedMode G n) ℂ :=
  open Classical in fun x j => if x.1 = j.1 then Bloch.cell x.2 j.2 else 0

lemma role : Tie σbranch σbranch ((fourier G n)ᵀ) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  by_cases he : i = j
  subst j
  rfl
  exact (h (if_neg he)).elim

lemma volumeFactor : brightness N = (N.val : ℂ) ^ 4 := by
  simp only [brightness, scaleZ, νt]
  push_cast
  rw [inv_inv]

private lemma remap_l {A B C : Type} (F : Cyl A ℂ) (X : B → A → ℂ) (g : C → B) (w : List C) :
    shade (X ∘ g) F w = shade X F (w.map g) := by
  induction w generalizing F with
  | nil => simp
  | cons i l ih =>
    obtain ⟨s, hs⟩ := fromCyl F
    rw [deriv_lum _ i _ hs, List.map_cons, deriv_lum _ _ F hs]
    exact Finset.sum_congr rfl fun a ha => congr_arg (X (g i) a * ·) (ih _)

private lemma twist_l {A B : Type} {T X : B → A → ℂ} (V : Cyl A ℂ) (b : B → ℂ)
    (h : ∀ i j, T i j = b i * X i j) (w : List B) : shade T V w = (w.map b).prod * shade X V w := by
  induction w generalizing V with
  | nil => simp
  | cons i w ih =>
    obtain ⟨s, hs⟩ := fromCyl V
    simp only [deriv_lum T _ V hs, h, ih, List.map_cons, List.prod_cons, deriv_lum X _ V hs,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Removing the stencil offset in `Tone.run`. -/
lemma bareFourier (F : Dot G Cover) (w : List (FixedMode G N)) :
    specialize (fourier G N) (enters N F) w = sleeve lace (Tone.run F) (Orbit.stage w) := by
  let v := shown N F
  let T := fourier G N
  let U := Tone.Mesh.hint (G := G) N ∘ addr (n := N)
  let b : FixedMode G N → ℂ := lace ∘ addr
  change specialize T v.val w = _
  have ht (i : FixedMode G N) (x : LightMode G (Site N)) : Tᵀ i x = b i * U i x := by
    classical
    by_cases he : x.1 = i.1
    swap
    · change (fourier G N) x i = _ * (way _ _ _ * _)
      rw [show fourier G N x i = 0 from if_neg he, need id (Ne.symm he), zero_mul, mul_zero]
    rcases x with ⟨z, x⟩
    rcases i with ⟨k, p⟩
    dsimp only at he
    subst k
    let X := Coord p
    rw [show (Tᵀ) (z, p) (z, x) = cell x p from if_pos rfl]
    change _ = lace (z, X) * paywave (z, X) (z, Lattice.lift x)
    rw [pw, rightadd]
    rw [mul_left_comm _ (Tone.bill ..), (mul_comm (lace _)),
      (show Tone.bill X (offset z.1) * lace (z, X) = 1 from lace_ (z, X)), mul_one]
    rw [Tone.rights]
    unfold X
    rw [Orbit.dual_cell, wrap_lift, cell_duality]
  have hh : ∀ i ∈ Orbit.stage w, i.2 ∈ Tone.Mesh.proper N := by
    intro i hi
    obtain ⟨j, hk, rfl⟩ := List.mem_map.mp hi
    exact ⟨Lattice.lift j.2, rfl⟩
  rw [specialize_shade,
    show shade Tᵀ v w = (w.map b).prod * shade U v w from
      twist_l v b (show ∀ i j, Tᵀ i j = _ from ht) w,
    sleeve_here,
    show shade U v w = Tone.run F (Orbit.stage w) from
      (remap_l v ..).trans (Tone.Mesh.project F N _ hh)]
  congr 2
  exact (List.map_map ..).symm

lemma mark_fourier (F : Dot G Cover) (A x : Cover) :
    Mark_T G N A x F = specialize (fourier G N) (enters N (Lab.Shift (A + x) F)) := by
  ext w
  change Orbit.anchor G N A (frameL x (Tone.run F)) w = _
  rw [bareFourier G N, chase_now, Orbit.point, f_l, lodg, sleeve_here, sleeve_here]
  rw [Tone.movement, φ_s, Tone.rights (net _), ← be, be_add]
  ring

lemma sumCell (p : Site n) : ∑ x : Site n, cell p x = if p = 0 then brightness n else 0 := by
  split
  next h =>
    rw [volumeFactor n]
    subst p
    simp [cell]
  next h => exact Bloch.sum_cell h

lemma unmarked_fourier (F : Dot G Cover) :
    specialize (fourier G N) (docket N F) = Bulk G N (sleeve lace (Tone.run F)) := by
  let T := fourier G N
  ext w
  change specialize T (sumHome (shown N F)).val w = _
  rw [total_uses, sum_stack, map_sum, Finset.sum_apply]
  let V := sleeve lace (Tone.run F)
  let y := net w
  let W := Orbit.stage w
  have he x : specialize T (Lab.Shift x (shown N F)).val w = cell y x * V W := by
    rw [show Lab.Shift x (shown N F) = shown N (Lab.Shift (Lattice.lift x) F) from
        (by
          unfold shown
          rw [trans_shift, wrap_lift])]
    change specialize T (enters N (Lab.Shift (Lattice.lift x) F)) w = _
    rw [show specialize T _ w = _ from bareFourier G N (Lab.Shift (Lattice.lift x) F) w]
    unfold V W y
    simp only [sleeve_here, Tone.movement, mul_left_comm (hook ..)]
    congr 1
    have hz := (φ_s w (Lattice.lift x))
    unfold be Φa at hz
    rw [wrap_lift, cell_duality, Tone.rights] at hz
    exact hz.symm
  simp_rw [he]
  rw [← Finset.sum_mul, sumCell, bulkZ]
  dsimp only [y]
  split <;>
    first
    | rfl
    | simp [*]
end YM.WilsonMS.Position
