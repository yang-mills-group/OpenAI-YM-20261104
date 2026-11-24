import YM.Integration.WilsonPosteriorProjectionTaylor
import YM.Integration.WilsonConditionalMomentJets

/-! On the true selected Wilson kernel the complete one-variable derivative
bill on a prescribed ray is paid by its actual bounded fine test. The edge
sum is the sum of that one Lie direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionConditional
open Finset Set MeasureTheory Lattice Wilson RG Precision Tree Exterior Push.Uniform
open RG01.Kernel RG01.Kernel.Wheel WardBin.Lies WilsonPosteriorProjectionRay
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side}

private theorem shift (V : Config G c) (a : Directions G c) (s t : ℝ) :
    increment (increment V (t • a)) (s • a) = increment V ((s+t) • a) := by
  funext i
  apply G.mat_injective
  simp only [increment,G.mat_mul,Pi.smul_apply,G.mat_lieExp,map_smul,add_smul,map_add,← mul_assoc]
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply congr_arg (fun x => x * G.mat (V i))
  exact (NormedSpace.exp_add_of_commute (((Commute.refl (G.colorMat (a i))).smul_left s).smul_right t)).symm

private theorem raySmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Config G c → E) (q : ℕ) (g : ℝ) (z : Positions (Primary c G))
    (germ : ∀ V, Germ q F V) :
    ContDiff ℝ q (fun t : ℝ => F (represent (tint G _ (g • (t • z))))) := by
  simp_rw [field]
  rw [contDiff_iff_contDiffAt]
  intro t
  let a := direction g z
  let h := fun p => F (increment (increment 1 (t • a)) p)
  let k := fun s : ℝ => (s-t) • a
  have hk : ContDiffAt ℝ q k t := (contDiffAt_id.sub contDiffAt_const).smul contDiffAt_const
  have hh : ContDiffAt ℝ q h (k t) := by
    have zero : k t = 0 := by simp [k]
    rw [zero]
    exact germ _
  have eq : (fun s : ℝ => F (increment 1 (s • a))) = h ∘ k := by
    funext s
    dsimp only [Function.comp_apply,h,k]
    rw [shift,sub_add_cancel]
  exact eq ▸ hh.comp t hk

variable (H : History G) (sel : H.Selected) {N n m : ℕ} (hm : m<N)
variable {F : (H.levels.clock.op m n).Choices → Config G (H.S.side (m+1) n) → ℂ}
variable {b : ℝ} (bounded : Bounded (prior G (H.S.side (m+1) n)) F b) (hb : 0≤b)

include sel hm bounded hb in
theorem measured (g : ℝ) (z : Positions (Primary (H.S.side m n) G)) (q : ℕ) :
    let f := fun V => conditional H N m n V F
    let E := fun i => ‖direction g z i‖
    let h := fun t : ℝ => f (represent (tint G _ (g • (t • z))))
    ContDiff ℝ q h ∧ ∀ t, ‖iteratedDeriv q h t‖ ≤
      bill H E N (m+1)^q * compensation G q (invoice q b) (1+2*1) := by
  intro f E h
  let a := direction g z
  let l := List.replicate q a
  have e : ∀ v ∈ l, ∀ i, ‖v i‖ ≤ E i := by
    intro v hv i
    rw [List.eq_of_mem_replicate hv]
  have pay (V : Config G (H.S.side m n)) :=
    angular H sel V hm bounded hb l E (fun _ => norm_nonneg _) e
  constructor
  · apply raySmooth f q g z
    intro V
    simpa only [l,List.length_replicate] using (pay V).1
  · intro t
    rw [show iteratedDeriv q h t = _ from derivative f g z q t]
    simpa only [l,List.length_replicate] using (pay _).2.2

end YM.Integration.WilsonPosteriorProjectionConditional

