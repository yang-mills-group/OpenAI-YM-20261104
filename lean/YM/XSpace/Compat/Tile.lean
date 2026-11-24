import YM.Further.FREE_COVARIANCE_KP.KP.Native
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Mesh-integration helpers recovered from the hash-pinned Oct15 source.
The original covariance/symbol/Weight definitions retain their baseline identity.
New helper declarations live only in this compatibility namespace. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision
open scoped Topology ContDiff BigOperators InnerProductSpace Real ComplexConjugate
variable {ι : Type*} {n : Side} {α Ω η : ℝ}
def room (n : Side) (x : Cover) : Set E4 := {p | mark (leap n) p=x}
def pick (n : Side) (p : E4) := lit n (mark (leap n) p)
def slab (n : Side) (x : ℤ) := Ico (leap n*x) (leap n*((x:ℝ)+1))
private lemma basic_room (n) (x:Cover) : room n x = WithLp.ofLp ⁻¹' pi univ (fun i => slab n (x i)) := by
  ext p
  simp only [room,mark,slab,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_true_left,funext_iff,Int.floor_eq_iff,le_div_iff₀ (leap_pos _),div_lt_iff₀ (leap_pos _),mem_Ico,mul_comm]

lemma room_paid (n : Side) (x : Cover) : MeasurableSet (room n x) ∧ volume (room n x)=ENNReal.ofReal ((leap n)^4) := by
  rw [basic_room]; have hh := PiLp.volume_preserving_ofLp Axis
  have he : MeasurableSet (pi univ (fun i => slab n (x i))) := MeasurableSet.pi countable_univ fun i _ => measurableSet_Ico
  refine ⟨hh.measurable he,?_⟩
  rw [hh.measure_preimage he.nullMeasurableSet]
  change Measure.pi _ _=_
  rw [Measure.pi_pi]
  have ht (k:ℤ) : volume (slab n k)=ENNReal.ofReal (leap n) := by
    unfold slab
    rw [Real.volume_Ico]
    congr 1
    ring
  simp_rw [ht]; simp [ENNReal.ofReal_pow (leap_pos n).le]
lemma pick_near (n : Side) (p : E4) : ‖pick n p - p‖ ≤ 2*leap n := by
  have ht:=leap_pos n
  apply le_of_sq_le_sq _ (by positivity); rw [PiLp.norm_sq_eq_of_L2]; calc
    _ ≤ ∑ _ : Axis, (leap n)^2 := Finset.sum_le_sum fun i _=> pow_le_pow_left₀ (norm_nonneg _) (marked_bound ht p i) _
    _ = _ := by simp; ring

theorem clip_pay (n) (f:E4→ℂ) :
    Integrable (fun p=> house (pick n p) * f (pick n p)) ∧
    ∫ p:E4, house (pick n p)*f (pick n p) = (leap n)^4 • ∑ i: Site n×St, house (lit n (pav n i))*f (lit n (pav n i)) := by
  let G (x:Cover) := house (lit n x)*f (lit n x)
  let F (i : Site n × St) := (room n (pav n i)).indicator (fun _=> G (pav n i))
  have hh (p:E4) : house (pick n p)*f (pick n p) = ∑ i : Site n×St, F i p := by
    let x := mark (leap n) p; change G x=_
    by_cases h : ∃ i,pav n i=x
    · obtain ⟨i,hi⟩ := h
      rw [Finset.sum_eq_single i,show F i p=G x from (indicator_of_mem (show p∈room n (pav n i) from hi.symm) _).trans (congr_arg G hi)]
      intro j _ hj
      exact indicator_of_notMem (show p∉room n (pav n j) from fun hh=> hj (pav_sep n (hh.symm.trans hi.symm))) _
      simp
    rw [Finset.sum_eq_zero]
    unfold G
    rw [show house (lit n x)=0 from by_contra fun e=>h (roof_hit x e),zero_mul]
    intro i _
    exact indicator_of_notMem (fun hh=> h ⟨i, (show _=pav n i from hh).symm⟩) _
  have hb (i : Site n×St) : Integrable (F i) := by
    obtain ⟨ht,hb⟩ := room_paid n (pav n i)
    apply IntegrableOn.integrable_indicator _ ht
    exact integrableOn_const (hb ▸ ENNReal.ofReal_ne_top)
  have hv i : ∫ p:E4,F i p = (leap n)^4 • G (pav n i) := by
    obtain ⟨ht,hb⟩:=room_paid n (pav n i)
    unfold F
    rw [integral_indicator ht,setIntegral_const, measureReal_def,hb, ENNReal.toReal_ofReal (pow_nonneg (leap_pos n).le _)]
  simp_rw [hh]; rw [integral_finsetSum _ (fun i _ => hb i),Finset.smul_sum]; simp_rw [hv]; exact ⟨integrable_finsetSum _ (fun i _=>hb i),rfl⟩
end YM.XSpace.Compat.KP
end
