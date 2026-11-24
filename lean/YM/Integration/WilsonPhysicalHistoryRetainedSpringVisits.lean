import YM.Integration.WilsonPhysicalHistoryRetainedSpringTaylor
import YM.Integration.QLocalMeasuredPathMoments

/-! All visits of the original ordered curvature word use one common
measure, including repeated visits and a tester absorbed into that measure. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Lattice RG Wilson Finset MeasureTheory WilsonMeasuredPathTaylor
open FundedCurvatureRayTaylor WilsonSlotContactTruncation
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]

theorem contact_size (a : Atom G k) (x : Site n) (b : Fin k→G.ColorIndex) :
    (contacts x (letters a b)).length≤2*a.length := by
  rw [length_contacts]
  simp only [letters,List.map_ofFn,List.sum_ofFn,Function.comp_apply,Atom.length,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _=>by
    change (a.leg i).length+(a.leg i).walk.length≤2*(a.leg i).length
    unfold Slot.length
    omega

theorem score_moment (μ : Measure Ω) (v : Ω→Directions G n) (q : ℕ) {M : ℝ} (pos : 0<M)
    (a : Atom G k) (x : Site n) (b : Fin k→G.ColorIndex)
    (measured : ∀ e∈contacts x (letters a b),AEStronglyMeasurable (fun z=>speed (v z) e) μ)
    (thermal : ∀ e∈contacts x (letters a b),
      Integrable (fun z=>speed (v z) e^(q+1)) μ ∧
        (∫ z,speed (v z) e^(q+1) ∂μ)≤M^(q+1)) :
    Integrable (fun z=>score (v z) x (letters a b)^(q+1)) μ ∧
      (∫ z,score (v z) x (letters a b)^(q+1) ∂μ)≤(2*(a.length:ℝ)*M)^(q+1) := by
  let l:=contacts x (letters a b)
  let f (i : Fin l.length) (z : Ω):=speed (v z) (l.get i)
  have repr (z : Ω) : ∑ i,f i z=score (v z) x (letters a b) := by
    change ∑ i : Fin l.length,speed (v z) (l.get i)=(l.map (speed (v z))).sum
    have perm : List.ofFn (speed (v z) ∘ l.get)=l.map (speed (v z)) := by
      rw [←List.map_ofFn,List.ofFn_get]
    rw [←perm,List.sum_ofFn]
    rfl
  have input (i : Fin l.length) : l.get i∈contacts x (letters a b):=List.get_mem ..
  have all := QLocalMeasuredPathMoments.pooled μ Finset.univ (fun _ : Fin l.length=>M) f
    (fun _ _=>pos) (fun i _ z=>show 0≤‖G.colorMat (v z (l.get i))‖ from norm_nonneg _) (fun i _=>measured _ (input i)) q
    (fun i _=>thermal _ (input i))
  dsimp only at all
  simp only [repr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at all
  exact ⟨all.1,all.2.trans (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast contact_size a x b) pos.le) _)⟩

end YM.Integration.OriginalMarkedRunAction
