import YM.Integration.WilsonAllDateHarvestClearance

/-! A compact smooth physical test off the colour diagonals has a common
positive separation, a finite root range and finite derivative seminorms. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedTestControl
open Function Filter Finset Set RG05Readout RG05Readout.Native RG05Readout.Pulse RG05Readout.Nuclear
open scoped Topology Classical BigOperators

variable {W:Type} [Fintype W] (Ψ:Wave W) (compact:IsCompact (tsupport Ψ.val))
include compact

theorem separation (apart:∀x∈tsupport Ψ.val,Injective x) :
    ∃η:ℝ,0 < η ∧ η ≤ 1 ∧ Pulse.Scattering Ψ η := by
  by_cases present:(tsupport Ψ.val).Nonempty
  · have near (i j:W):∀ᶠ q:ℝ in 𝓝[>]0,
        i≠j → ∀x∈tsupport Ψ.val,q ≤ ‖x i-x j‖ := by
      by_cases equal:i=j
      · exact Filter.Eventually.of_forall (fun _ ne=>(ne equal).elim)
      have continuous:Continuous (fun x:Pulse.Cloud W=>‖x i-x j‖):=
        ((continuous_apply i).sub (continuous_apply j)).norm
      obtain ⟨a,ha,minimal⟩:=compact.exists_isMinOn present continuous.continuousOn
      have pos:0 < ‖a i-a j‖:=norm_pos_iff.mpr (sub_ne_zero.mpr (fun h=>equal (apart _ ha h)))
      filter_upwards [((tendsto_id : Tendsto id (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ))).mono_right
        nhdsWithin_le_nhds).eventually_lt_const pos] with q small
      exact fun _ _ hx=>small.le.trans (minimal hx)
    have all:=Filter.eventually_all.mpr (fun i:W=>Filter.eventually_all.mpr (near i))
    have small:∀ᶠ q:ℝ in 𝓝[>]0,q < 1:=by
      exact (tendsto_id.mono_right nhdsWithin_le_nhds).eventually_lt_const zero_lt_one
    have positive:∀ᶠ q:ℝ in 𝓝[>]0,0<q:=self_mem_nhdsWithin
    obtain ⟨η,both,lt⟩:=(all.and (positive.and small)).exists
    exact ⟨η,lt.1,lt.2.le,fun x hx i j ne=>both i j ne x hx⟩
  · exact ⟨1,zero_lt_one,le_rfl,fun x hx=>False.elim (present ⟨x,hx⟩)⟩

theorem range :
    ∃R:ℝ,0 ≤ R ∧ ∀x∈tsupport Ψ.val,∀v:W,‖x v‖ ≤ R := by
  obtain ⟨R,priced⟩:=compact.exists_bound_of_continuousOn (f:=id) continuous_id.continuousOn
  exact ⟨max 0 R,le_max_left ..,fun x hx v=>(norm_le_pi_norm x v).trans
    ((priced x hx).trans (le_max_right ..))⟩

theorem derivatives (s:ℕ) : ∃X:ℝ,0 < X ∧ Nuclear.Tall Ψ s 1 X := by
  have each (i:Fin (s+1)) : ∃c:ℝ,0 ≤ c ∧ ∀z,‖iteratedFDeriv ℝ i.val Ψ.val z‖ ≤ c := by
    obtain ⟨c,cap⟩:=compact.exists_bound_of_continuousOn
      ((Pulse.lit Ψ i.val).continuous_iteratedFDeriv (m:=i.val) le_rfl).continuousOn
    refine ⟨max 0 c,le_max_left ..,?_⟩
    intro z
    by_cases h:z∈tsupport Ψ.val
    · exact (cap z h).trans (le_max_right ..)
    rw [notMem_support.mp (fun a=>h (support_iteratedFDeriv_subset i.val a)),norm_zero]
    exact le_max_left ..
  choose c pos pay using each
  refine ⟨1+∑i,c i,add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _=>pos i)),?_⟩
  intro i hi z
  rw [one_pow,one_mul]
  exact (pay ⟨i,by omega⟩ z).trans ((Finset.single_le_sum (fun i _=>pos i) (Finset.mem_univ _)).trans
    (le_add_of_nonneg_left zero_le_one))

end YM.Integration.WilsonMixedTaggedTestControl
