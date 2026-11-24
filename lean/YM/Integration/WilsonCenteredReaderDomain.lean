import YM.Integration.WilsonCenteredBornHearing
import YM.OPE.Orbits.Separated

/-! The compact smooth near test stays in one original reader window, including
the integration domain on which the physically measured coefficients are smooth. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredReaderDomain
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction OPE OPE.Orbits
open scoped Classical Topology BigOperators
variable {n:ℕ}

theorem room (φ:Test n) :
    ∃ M:ℝ,0≤M ∧ ∃ η:ℝ,0<η ∧ ∀ r:ℝ,0<r→∀ x∈tsupport (φ:Points n→ℂ),
      WithinRoom r M η (r•x).ofLp 0 :=by
  let K := tsupport (φ:Points n→ℂ)
  obtain ⟨A,cap⟩:=φ.hasCompactSupport.isBounded.exists_norm_le
  have edge (i j:Fin n) : ∃e:ℝ,0<e ∧ ∀x∈K,i≠j→e ≤ ‖x i-x j‖ :=by
    by_cases occupied : K.Nonempty
    · by_cases eq : i=j
      · exact ⟨1,zero_lt_one,fun _ _ h=>(h eq).elim⟩
      have cont : Continuous (fun x:Points n=>‖x i-x j‖) :=by fun_prop
      obtain ⟨x,hx,low⟩:=φ.hasCompactSupport.exists_isMinOn occupied cont.continuousOn
      exact ⟨_,norm_pos_iff.mpr (sub_ne_zero.mpr ((φ.tsupport_subset hx).ne eq)),fun y hy _=>low hy⟩
    · exact ⟨1,zero_lt_one,fun x hx _=>(occupied ⟨x,hx⟩).elim⟩
  choose e pos bill using edge
  have near : ∀ᶠ η:ℝ in 𝓝 0,∀ i j,η<e i j := eventually_all.mpr fun i=>
    eventually_all.mpr fun j=>Iio_mem_nhds (pos i j)
  have small : ∀ᶠ η:ℝ in 𝓝[>] 0,∀i j,η<e i j :=near.filter_mono nhdsWithin_le_nhds
  obtain ⟨η,fit,hη⟩:=(small.and self_mem_nhdsWithin).exists
  refine ⟨max 0 A,le_max_left _ _,η,hη,fun r hr x hx=>⟨fun i=>?_,fun i j h=>?_⟩⟩
  · change ‖r • x i - 0‖ ≤ max 0 A*r
    rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_comm]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le x i).trans ((cap x hx).trans (le_max_right 0 A))) hr.le
  · change η*r ≤ ‖r • x i - r • x j‖
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_comm η]
    exact mul_le_mul_of_nonneg_left ((fit i j).le.trans (bill i j x hx h)) hr.le

variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}

/-- The physical reader's finite aperture is available simultaneously on the
whole test support. Its original openness gives smooth measured packets there. -/
theorem dock (F:Spec.Final C f S) (A:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (φ:Test n) (h:ℕ) :
    ∀ᶠ r:ℝ in 𝓝[>] 0,∀ x∈tsupport (φ:Points n→ℂ),orbitMargin A.port h (r•x).ofLp 0 :=by
  obtain ⟨M,mp,η,eta,housed⟩:=room φ
  filter_upwards [admissible_separated F A (I:=Fin n) mp eta h,self_mem_nhdsWithin] with r safe hr
  exact fun x hx=>safe _ 0 (housed r hr x hx) h le_rfl

end YM.Integration.WilsonCenteredReaderDomain
