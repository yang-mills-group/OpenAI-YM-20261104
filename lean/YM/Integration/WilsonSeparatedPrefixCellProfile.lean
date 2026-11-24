import YM.Integration.WilsonAddressedPhysicalCells
import YM.Integration.WilsonMovingForkClearance

/-! The actual joint right-closed cells of a separated test have one total variation charge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCellProfile
open Function Set Filter Finset MeasureTheory Lattice Extraction RG
open WilsonAddressedPhysicalCells
open private visible from YM.Integration.WilsonAddressedPhysicalCells
open scoped Classical BigOperators Topology

theorem active {n:ℕ}(φ:Test n)(a r:ℝ)(side:Side)(positive:0<a)(u:Sites side n)
    (occupied:mass φ a r side u≠0):∃x:Points n,atSite a r side x=u ∧ φ x≠0:=by
  by_contra! empty
  apply occupied
  calc
    _=∫(_x:Points n) in cell a r side u,(0:ℂ):=setIntegral_congr_fun (visible a r side positive u)
      (fun x hx=>empty x hx)
    _=0:=by simp

theorem shape {n:ℕ}(φ:Test n):∃M η:ℝ,0<M ∧ 0<η ∧ ∀x:Points n,φ x≠0→
    (∀i,‖x i‖≤M) ∧ Pairwise fun i k=>η≤‖x i-x k‖:=by
  obtain ⟨M,fits,pos⟩:=((Work.A05.compact_fits φ.hasCompactSupport φ.tsupport_subset).and
    (eventually_gt_atTop (0:ℝ))).exists
  refine ⟨M,M⁻¹,pos,inv_pos.mpr pos,?_⟩
  intro x active
  have limits:=fits (subset_closure active)
  obtain ⟨apart,width⟩:=limits
  refine ⟨fun i=>(PiLp.norm_apply_le x i).trans width,?_⟩
  intro i k ne
  apply (apart i k ne).trans
  unfold cubedist
  rw [dist_eq_norm,pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro k';exact PiLp.norm_apply_le (x i-x k) k'

theorem tested {n:ℕ}(φ:Test n)(a r:ℝ)(side:Side)(positive:0<a)(D:Sites side n→ℂ):
    φ.applyTo (fun x=>D (atSite a r side x))=∑u,mass φ a r side u*D u:=by
  have finite:Integrable (fun x:Points n=>φ x):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  unfold Test.applyTo
  rw [integrate a r side positive (fun u x=>φ x*D u) (fun u=>finite.mul_const (D u))]
  exact Finset.sum_congr rfl (fun u _=>integral_mul_const _ _)

theorem priced {n:ℕ}(φ:Test n)(a r:ℝ)(side:Side)(positive:0<a)(D:Sites side n→ℂ)(ε:ℝ)(hp:0≤ε)
    (sold:∀u,mass φ a r side u≠0→‖D u‖≤ε):
    ‖φ.applyTo (fun x=>D (atSite a r side x))‖≤(∫x,‖φ x‖)*ε:=by
  rw [tested φ a r side positive D]
  calc
    _ ≤ ∑u,‖mass φ a r side u*D u‖:=norm_sum_le ..
    _ ≤ ∑u,‖mass φ a r side u‖*ε:=by
      apply Finset.sum_le_sum
      intro u _
      by_cases no:mass φ a r side u=0
      · simp [no]
      · rw [norm_mul];exact mul_le_mul_of_nonneg_left (sold _ no) (norm_nonneg _)
    _ = (∑u,‖mass φ a r side u‖)*ε:=by rw [Finset.sum_mul]
    _ ≤ _:=mul_le_mul_of_nonneg_right (total φ a r side positive) hp

end YM.Integration.WilsonSeparatedPrefixCellProfile
end
