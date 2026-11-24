import YM.WilsonMS.Top.Straight

/-! # Inversion-image kernel; signs are for *oriented* links, shift by one site.

Separate momentum reflection on `Swirl` letters from physical-site `θ`.
No signs on scalar site ghosts. -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open Function Filter Finset Set Matrix Complex Lattice
open MS MS.Koszul MS.Plane MS.Native MS.Orbit MS.Orbit.Cog
open MS.Book MS.Landau MS.Latch MS.Swirl MS.Swirl.Near MS.Tone Bloch
open scoped Topology

variable (G : Gauge) (n : Side)
local notation "Γ" => fourier G n
local notation "O" => iota G n

def reflect (w : FixedMode G n) : FixedMode G n :=
  match w with
  | (((some i, b), x), u) => (((some i, b), x), -u - step i)
  | (((none, b), x), u) => (((none, b), x), -u)

def scalarSign (x : FixedMode G n) : ℂ :=
  if x.1.1.1.isNone then 1 else -1

lemma phase_image (i j : FixedMode G n) :
    Γ i ((O).mode j) * (O).spin j = scalarSign G n i * Γ (reflect G n i) j := by
  classical
  rcases i with ⟨⟨⟨_ | i, b⟩, s⟩, x⟩
  all_goals rcases j with ⟨j, p⟩
  · by_cases h : j = ((none, b), s)
    swap
    · simp [fourier, iota_mode, reflect, Ne.symm h]
    subst j
    have hg : ∀ q : Lane4 G, (q.1.1.1 = none) → gscore q = 1 := by
      rintro ⟨⟨⟨_ | a, _ | _⟩, c⟩, z⟩ h <;>
        first
        | rfl
        | contradiction
    rw [iota_mode, iota_spin, switch, hg]
    swap
    · rfl
    rw [show lace (addr ((((none, b), s), p) : FixedMode G n)) = 1 from Tone.right0 (-Coord p)]
    rw [one_pow, one_mul, mul_one]
    change fourier _ _ _ _ = 1 * fourier G n (((none, b), s), -x) (((none, b), s), p)
    unfold fourier
    simp only [ite_true, one_mul]
    rw [cell_duality (-x), cell_inverse, cell_inverse, cell_duality p x]
  by_cases h : j = ((some i, b), s)
  swap
  · simp [fourier, iota_mode, reflect, Ne.symm h]
  subst j
  rw [iota_mode, iota_spin, switch]
  change Γ _ _ * ((-1 : ℂ) * midPhase (-Coord p) i ^ 2) = -1 * Γ _ _
  have ht : midPhase (-Coord p) i ^ 2 = cell p (-step i) := by
    unfold midPhase
    rw [pow_two, ← rightadd, ←
      (show
        Tone.embed (step i) = (1 / 2 : ℝ) • Tone.embed (step i) + (1 / 2 : ℝ) • Tone.embed (step i)
        from Tone.Frame.centr i)]
    rw [opp, Tone.rights (Coord p), Orbit.dual_cell, wrap_step, cell_inverse]
  rw [ht]
  unfold fourier reflect
  dsimp only
  simp only [ite_true]
  rw [cell_duality _ p, sub_eq_add_neg, cell_add, cell_inverse x p, cell_inverse p x,
    cell_duality p x]
  ring

lemma induced_mirror (K : Grain (FixedMode G n)) (i j : FixedMode G n) :
    induce Γ (imageW (O) K) i j = scalarSign G n j * induce Γ K i (reflect G n j) := by
  let S := (O)
  rw [induce_value, induce_value, Finset.mul_sum]
  let f (y : FixedMode G n) := ∑ x : FixedMode G n, Γ i x * imageW S K x y * Γ j y
  change (∑ y : FixedMode G n, f y) = _
  rw [← Equiv.sum_comp S.axis f]
  apply Finset.sum_congr rfl
  intro y _
  change (∑ x : FixedMode G n, Γ i x * imageW S K x (S.mode y) * Γ j (S.mode y)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [imageW, show S.mode (S.mode y) = y from S.perm y]
  linear_combination (norm := ring) (Γ i x * K x y) * phase_image G n j y

abbrev initialK : Grain (FixedMode G n) :=
  induce Γ (mat n (FinalK G))

abbrev foldedK : Grain (FixedMode G n) :=
  induce Γ (Master G n true)

lemma actual_image (x y : FixedMode G n) :
    foldedK G n x y = initialK G n x y + scalarSign G n y * initialK G n x (reflect G n y) := by
  rw [← induced_mirror]
  let K := mat n (FinalK G)
  change induce Γ (K + imageW (O) K) x y = induce Γ K x y + induce Γ (imageW (O) K) x y
  simp_rw [induce_value, Pi.add_apply, _root_.mul_add, _root_.add_mul, Finset.sum_add_distrib]

section sym
variable {T L K' : Type} [Fintype T] [Fintype L] {W : Matrix T L ℂ} {X : Grain L} {p : Sector T}
  {q : Sector L} (hp : Cog.Sym q X) (hn : MS.Cylinder.Tie p q Wᵀ)
omit G n
include hp hn

omit [Fintype T] in
lemma induces_sym : Cog.Sym p (induce W X) := by
  intro i j
  rw [induce_value, induce_value, sum_comm, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [mul_sum]
  refine sum_congr rfl (fun l _ => ?_)
  by_cases ht : W i k = 0
  rw [ht]
  ring
  by_cases hs : W j l = 0
  rw [hs]
  ring
  rw [hp k l, hn i k ht, hn j l hs]
  ring
end sym

lemma basic_symmetry : Cog.Sym σbranch (initialK G n) :=
  induces_sym (Near.paySym false) (role G (n := n))

lemma folded_symmetry : Cog.Sym σbranch (foldedK G n) :=
  induces_sym (Near.paySym true) (role G (n := n))
end YM.WilsonMS.Position
