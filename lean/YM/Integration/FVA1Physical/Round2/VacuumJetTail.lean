import YM.Integration.FVA1Physical.Round2.VacuumShells

/-! Localizing the field while testing every regular derivative simultaneously.
The geometry weight keeps half of the exponential for the tested addresses
and spends the other half on the distance of the changed field. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped BigOperators Classical Topology
variable {σ : Type} [Fintype σ] {n : Side}

omit [Fintype σ] in
private theorem split_weight {site : σ → Site n} {a : ℝ} (ha : 0 ≤ a) (s r : ℕ)
    (i j : σ) (l : List σ) (far : r ≤ separation (site i) (site j)) :
    Measuring.swipe site (a/2) s (i::l) * liftW (a/2) 0 r ≤
      Measuring.swipe site a s (i::j::l) := by
  let D := extent (zone site ∅ (i::j::l))
  have h₁ : extent (zone site ∅ (i::l)) ≤ D := by
    apply intr; intro x hx
    simp [zone] at hx ⊢
    rcases hx with hx|hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  have h₂ : r ≤ D := far.trans (curve (x := site i) (y := site j) (by simp [zone]) (by simp [zone]))
  have half : 0 ≤ a/2 := by positivity
  change liftW (a/2) s _ * _ ≤ liftW a s D
  refine (mul_le_mul (w_more h₁ half s) (w_more h₂ half 0) (wpos ..).le (wpos ..).le).trans_eq ?_
  simp only [liftW,pow_zero,one_mul,mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- The entire held-address weighted derivative row has a spatially decaying
tail. Its bound is uniform in the field, the size of the torus and the
number of coordinates changed outside radius r. -/
theorem rooted_jet_tail {site : σ → Site n} {a w B : ℝ} {s k q : ℕ}
    {S : Set (Positions σ)} {F : Positions σ → ℝ}
    (J : JetTab site a s w S F (q+1) B) (hw : 0 < w) (ha : 0 ≤ a)
    (hf : ∀ x ∈ S, ContDiffAt ℝ k F x) (hk : q+2 ≤ k) (i : σ)
    (r : ℕ) (x v : Positions σ) (stay : ∀ t ∈ Set.Icc (0:ℝ) 1, x+t • v ∈ S)
    (far : ∀ j, v j ≠ 0 → r ≤ separation (site i) (site j)) :
    Yarn q (fun l : List σ => |buoy F (x+v) (i::l)-buoy F x (i::l)| *
        Measuring.swipe site (a/2) s (i::l)) ≤
      ‖v‖ / w^(q+2) * B / liftW (a/2) 0 r := by
  obtain ⟨_,g,sup,row⟩ := J
  let P := w^(q+2)
  let W := liftW (a/2) 0 r
  have hP : 0 < P := pow_pos hw _
  have hW : 0 < W := wpos ..
  let wt := fun l : List σ => Measuring.swipe site a s (i::l)
  let localWt := fun l : List σ => Measuring.swipe site (a/2) s (i::l)
  let env := fun j (l : List σ) => g (i::j::l)*wt (j::l)
  let K := ‖v‖ / P
  have single (l : List σ) (hl : l.length = q) :
      |buoy F (x+v) (i::l)-buoy F x (i::l)| * localWt l ≤
        K * (∑ j, env j l) / W := by
    let A := fun z : Positions σ => buoy F z (i::l)
    let U := localWt l * W
    have hU : 0 < U := mul_pos (effect site _ s ∅ (i::l)) hW
    have length (j : σ) : (i::j::l).length = q+1+1 := by simp [hl]
    have smoothA (z : Positions σ) (hz : z ∈ S) : DifferentiableAt ℝ A z := by
      have sm := smooth k 1 ((i::l).map bolt) (hf z hz) (by simp [hl]; omega)
      exact sm.differentiableAt (by simp)
    have dir (z : Positions σ) (hz : z ∈ S) :
        ‖fderiv ℝ A z v‖ ≤ K * (∑ j,env j l) / U := by
      have eqj (j : σ) : fderiv ℝ A z (bolt j) = buoy F z (i::j::l) := by
        change roc F (bolt j :: bolt i :: l.map bolt) z = roc F (bolt i :: bolt j :: l.map bolt) z
        exact echo k (hf z hz) _ _ (by simp [hl]; omega) (List.Perm.swap _ _ _)
      apply (le_div_iff₀ hU).2
      calc
        ‖fderiv ℝ A z v‖ * U ≤ (∑ j : σ, ‖v j‖ * |buoy F z (i::j::l)|)*U := by
          apply mul_le_mul_of_nonneg_right _ hU.le
          nth_rw 1 [spiral v]; rw [map_sum]
          exact (norm_sum_le ..).trans_eq (Finset.sum_congr rfl fun j _ => by
            rw [map_smul,norm_smul,eqj]; rfl)
        _ ≤ ∑ j, K * env j l := by
          rw [Finset.sum_mul]; apply Finset.sum_le_sum
          intro j _
          have hj := sup (i::j::l) (length j)
          have price : |buoy F z (i::j::l)| ≤ g (i::j::l) / P := (le_div_iff₀ hP).2 (hj.2 z hz)
          have hwt : 0 ≤ wt (j::l) := (effect site _ s ∅ _).le
          by_cases inactive : v j = 0
          · rw [inactive,norm_zero,zero_mul,zero_mul]
            exact mul_nonneg (div_nonneg (norm_nonneg _) hP.le) (mul_nonneg hj.1 hwt)
          have hus : U ≤ wt (j::l) := split_weight ha s r i j l (far j inactive)
          calc
            ‖v j‖ * |buoy F z (i::j::l)| * U ≤
              ‖v‖ * (g (i::j::l) / P) * wt (j::l) :=
              mul_le_mul (mul_le_mul (norm_le_pi_norm v j) price (abs_nonneg _) (norm_nonneg _))
                hus hU.le (mul_nonneg (norm_nonneg _) (div_nonneg hj.1 hP.le))
            _ = _ := by dsimp only [K,env]; ring
        _ = _ := (Finset.mul_sum ..).symm
    have hd (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
        HasDerivAt (fun u : ℝ => A (x+u • v)) (fderiv ℝ A (x+t • v) v) t := by
      have inner : HasDerivAt (fun u : ℝ => x+u • v) v t := by
        simpa using ((hasDerivAt_id' t).smul_const v).const_add x
      exact (smoothA _ (stay t ht)).hasFDerivAt.comp_hasDerivAt t inner
    have integral := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t ht => dir _ (stay t (Set.Ico_subset_Icc_self ht)))
    have result : |A (x+v)-A x| * U ≤ K*(∑ j,env j l) :=
      (le_div_iff₀ hU).mp (by simpa [Real.norm_eq_abs] using integral)
    exact (le_div_iff₀ hW).2 (by simpa only [U,A,mul_assoc] using result)
  calc
    _ ≤ Yarn q (fun l : List σ => K*(∑ j, env j l)/W) := shiny q single
    _ = (K/W) * (∑ j, Yarn q (env j)) := by
      rw [← scarves q Finset.univ env, ← sheen]
      apply stitch
      intro l _; ring
    _ ≤ (K/W) * B := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (div_nonneg (norm_nonneg _) hP.le) hW.le)
      exact row i
    _ = _ := by dsimp [K,P,W]; ring

end YM.Integration.FVA1Physical.Round2
