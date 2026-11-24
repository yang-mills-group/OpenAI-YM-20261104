import YM.Integration.WilsonPosteriorProjectionMeasured
import YM.MSbar.LocalSD.Expect
import YM.Analysis.Homogeneous

/-! The physical tensor is the genuine multivariate Taylor coefficient of
the original MS-bar primitive at the zero coarse field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionGerm
open Finset Set MeasureTheory Lattice Wilson RG Precision Tree Exterior Push.Uniform
open RG01.Kernel RG01.Kernel.Wheel WardBin.Lies
open WilsonPosteriorProjectionRay WilsonPosteriorProjectionTaylor WilsonPosteriorProjectionHaar
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side}

private def embed : Positions (Primary c G) →ₗ[ℝ] Directions G c where
  toFun := fun z => collect G (tint G _ z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def angle (g : ℝ) : Positions (Primary c G) →L[ℝ] Directions G c :=
  g • embed.toContinuousLinearMap

variable (H : History G) (sel : H.Selected) {N n m : ℕ} (hm : m<N)
variable (φ : Config G (H.S.side (m+1) n) → ℝ)

def original (g : ℝ) (z : Positions (Primary (H.S.side m n) G)) : ℝ :=
  MSbar.Bulk.expect (H.levels.clock.op m n) (H.rep N n (m+1))
    (represent (tint G _ (g • z))) φ

theorem original_ray (g : ℝ) (z : Positions (Primary (H.S.side m n) G)) :
    (fun s : ℝ => original H (N:=N) φ g (s • z)) = ray (posterior H (N:=N) φ) g z := rfl

include sel hm in
theorem regular (g : ℝ) (q : ℕ) {b : ℝ} (funded : Bounded (prior G (H.S.side (m+1) n))
    (fun (_ : (H.levels.clock.op m n).Choices) U => ((φ U : ℝ) : ℂ)) b) (hb : 0≤b) :
    ContDiffAt ℝ q (original H (N:=N) φ g) 0 := by
  let f := fun V => conditional H N m n V (fun _ U => ((φ U : ℝ) : ℂ))
  let k := fun u : Directions G (H.S.side m n) => f (increment 1 u)
  let E := Directions G (H.S.side m n)
  let word := List.replicate q (0 : E)
  have bound : ∀ v ∈ word, ∀ i, ‖v i‖ ≤ (0:ℝ) := by
    intro v hv i
    rw [List.eq_of_mem_replicate hv]
    change ‖(0 : G.Color)‖ ≤ 0
    simp
  have base := (angular H sel 1 hm funded hb word (fun _ => 0) (fun _ => le_rfl) bound).1
  have smoothK : ContDiffAt ℝ q k 0 := by simpa only [k,f,Germ,word,List.length_replicate] using base
  let a : Positions (Primary (H.S.side m n) G) →L[ℝ] E := angle g
  have inner : ContDiffAt ℝ q (k ∘ a) 0 := by
    apply ContDiffAt.comp (g:=k) (f:=a)
    · simpa only [map_zero] using smoothK
    · exact a.contDiff.contDiffAt
  have eq : original H (N:=N) φ g = Complex.reCLM ∘ k ∘ a := by
    funext z
    change _ = (conditional H N m n (increment 1 (a z)) _).re
    rw [normalized H sel hm φ funded]
    rfl
  rw [eq]
  exact Complex.reCLM.contDiff.contDiffAt.comp 0 inner

theorem on_ray (g : ℝ) (q : ℕ) (z : Positions (Primary (H.S.side m n) G))
    (regular : ContDiffAt ℝ q (original H (N:=N) φ g) 0) :
    Tensor.diagonal (Tensor.coeff (original H (N:=N) φ g) q 0) z =
      row (ray (posterior H (N:=N) φ) g z) q := by
  rw [← original_ray H φ g z]
  unfold row Tensor.diagonal Tensor.coeff
  rw [Next.Foundations.iteratedDeriv_on_line regular z]
  simp only [smul_apply,Tensor.diagonal,smul_eq_mul,div_eq_mul_inv,mul_comm]

end YM.Integration.WilsonPosteriorProjectionGerm

