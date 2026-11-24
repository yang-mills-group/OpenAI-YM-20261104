import YM.Integration.FVA1Physical.Round2.VacuumLocality

/-! Mixed finite changes of actual weak-field coordinates. The same anchored
derivative envelope prices all the corners, including for a different
background or independent set of changes at each address tuple. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped BigOperators Classical Topology
variable {σ : Type} [Fintype σ]

def rectangle (h : σ → ℝ) : List σ → (Positions σ → ℝ) → Positions σ → ℝ
  | [], F, x => F x
  | i::l, F, x => rectangle h l F (x+h i • bolt i) - rectangle h l F x

def rectangleInside (h : σ → ℝ) (S : Set (Positions σ)) : List σ → Positions σ → Prop
  | [], x => x ∈ S
  | i::l, x => ∀ t ∈ Set.Icc (0:ℝ) 1, rectangleInside h S l (x+t • (h i • bolt i))

omit [Fintype σ] in
private theorem rectangle_scale (h : σ → ℝ) (l : List σ) (a : ℝ) (F : Positions σ → ℝ)
    (x : Positions σ) : rectangle h l (fun y => a*F y) x = a*rectangle h l F x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => simp only [rectangle, ih, mul_sub]

private theorem rectangle_deriv (h : σ → ℝ) (S : Set (Positions σ)) (F : Positions σ → ℝ)
    (hf : ∀ y∈S, DifferentiableAt ℝ F y) (l : List σ)
    (z : ℝ → Positions σ) (v : Positions σ) (t : ℝ)
    (hz : HasDerivAt z v t) (inside : rectangleInside h S l (z t)) :
    HasDerivAt (fun u=>rectangle h l F (z u))
      (rectangle h l (fun y=>fderiv ℝ F y v) (z t)) t := by
  induction l generalizing z with
  | nil => exact (hf _ inside).hasFDerivAt.comp_hasDerivAt t hz
  | cons i l ih =>
    have right : rectangleInside h S l (z t) := by simpa using inside 0 (by simp)
    have left : rectangleInside h S l (z t + h i • bolt i) := by simpa using inside 1 (by simp)
    exact (ih (fun u=>z u+h i • bolt i) (hz.add_const _) left).sub (ih z hz right)

theorem rectangle_price {S : Set (Positions σ)} {F : Positions σ → ℝ} {k : ℕ}
    (hf : ∀ y∈S, ContDiffAt ℝ k F y) (h : σ → ℝ) (moves held : List σ)
    (x : Positions σ) (inside : rectangleInside h S moves x)
    (room : moves.length+held.length ≤ k) (B : ℝ)
    (cap : ∀ y∈S, |buoy F y (moves.reverse++held)| ≤ B) :
    |rectangle h moves (fun y=>buoy F y held) x| ≤ (moves.map (fun i=>|h i|)).prod * B := by
  induction moves generalizing held x with
  | nil => simpa [rectangle] using cap x inside
  | cons i l ih =>
    let D := fun y=>buoy F y held
    let line := fun t : ℝ=>x+t • (h i • bolt i)
    let A := fun t : ℝ=>rectangle h l D (line t)
    let d := fun t : ℝ=>h i*rectangle h l (fun y=>buoy F y (i::held)) (line t)
    have diff (y : Positions σ) (hy : y∈S) : DifferentiableAt ℝ D y := by
      have H := smooth k 1 (held.map bolt) (hf y hy) (by simp only [List.length_map]; simp only [List.length_cons] at room; omega)
      exact H.differentiableAt (by simp)
    have hd (t : ℝ) (ht : t∈Set.Icc 0 1) : HasDerivAt A (d t) t := by
      have hz : HasDerivAt line (h i • bolt i) t := by
        simpa [line] using ((hasDerivAt_id' t).smul_const (h i • bolt i)).const_add x
      have H := rectangle_deriv h S D diff l line _ t hz (inside t ht)
      have E : (fun y=>fderiv ℝ D y (h i • bolt i)) = fun y=>h i*buoy F y (i::held) := by
        funext y; rw [map_smul]; rfl
      rwa [E,rectangle_scale] at H
    have price (t : ℝ) (ht : t∈Set.Icc 0 1) :
        ‖d t‖ ≤ |h i| * ((l.map (fun j=>|h j|)).prod*B) := by
      rw [show d t = _ from rfl, Real.norm_eq_abs, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact ih (i::held) (line t) (inside t ht)
        (by simp only [List.length_cons] at room ⊢; omega)
        (by simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using cap)
    have H := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht=>(hd t ht).hasDerivWithinAt)
      (fun t ht=>price t (Set.Ico_subset_Icc_self ht))
    simpa only [Real.norm_eq_abs,A,line,D,one_smul,zero_smul,add_zero,rectangle,
      List.map_cons,List.prod_cons,mul_assoc] using H

end YM.Integration.FVA1Physical.Round2
