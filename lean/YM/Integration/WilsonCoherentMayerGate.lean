import YM.Integration.WilsonCoherentMayerTariff

/-! A marked ordinary address with its physical cutoff and full cohort left in
place. Removing its marked ingredient preserves its original local guard.
Unselected regular and forced leaves are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerGate
open Function Lattice RG Finset MeasureTheory Wilson Tree
open PhysicalNext.Repeat.Lotus
open scoped BigOperators Classical
variable {G:Gauge} {c f:Side} {R:Rep G f}

/-- The unit deposited on the original blank ordinary address and only on
the part of configuration space where that address may be occupied. -/
def resident (R:Rep G f) (i:ℕ) (blank:R.activities.E i=0) : Leaf R where
  turn := .logKey i
  ingredient := masked R.p.threshold (R.activities.reg i).support (fun _=> (1:ℝ))
  scopedR := by
    intro U V _ hv
    change (R.activities.reg i).support ∩ flags R.p.threshold U = (R.activities.reg i).support ∩ flags R.p.threshold V at hv
    have hh : Healthy R.p.threshold (R.activities.reg i).support U ↔
        Healthy R.p.threshold (R.activities.reg i).support V := by
      unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,hv,Finset.disjoint_iff_inter_eq_empty]
    by_cases h : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (hh.mp h)]
    · rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt hh.mpr h)]
  grant := by
    intro U value
    by_contra h
    exact value (masked_ne _ _ _ _ h)
  blank := blank
  weight := 1
  earn := by
    intro U; by_cases h: Healthy R.p.threshold (R.activities.reg i).support U
    · rw [masked_eq _ _ _ _ h]; simp
    · rw [masked_ne _ _ _ _ h]; simp
  glows := by
    intro q U
    have hh : Healthy R.p.threshold (R.activities.reg i).support (gauge q U) ↔
        Healthy R.p.threshold (R.activities.reg i).support U := by unfold Healthy;rw [gauge_flags]
    by_cases h : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [masked_eq _ _ _ _ (hh.mpr h),masked_eq _ _ _ _ h]
    · rw [masked_ne _ _ _ _ (mt hh.mp h),masked_ne _ _ _ _ h]
  borel := masked_measurable _ _ _ measurable_const

def clear (v:Leaf R) : Leaf R :=
  match h:v.turn with
  | .logKey i => resident R i (by simpa [h,Wing.blank] using v.blank)
  | .gasKey _ => v

theorem same (v:Leaf R) : (clear v).turn=v.turn := by
  unfold clear;split <;> simp_all [resident]

theorem regular {v:Leaf R} {i:ℕ} (h:v.turn=.logKey i) (U:Config G f) :
    (clear v).weight=1 ∧ (clear v).ingredient U=
      masked R.p.threshold (R.activities.reg i).support (fun _=> (1:ℝ)) U :=by
  unfold clear; split <;> simp_all [resident]

def place (chosen:Finset (Leaf R)) (v:Leaf R) : Leaf R := if v∈chosen then clear v else v

theorem address (chosen:Finset (Leaf R)) (v:Leaf R) : (place chosen v).turn=v.turn :=by
  by_cases h:v∈chosen <;> simp [h,place,same]

/-- Use precisely the same named addresses on the actual representation. -/
def team (prior:Team R) (chosen:Finset (Leaf R)) : Team R where
  own := prior.own.image (place chosen)
  alone := by
    intro x hx y hy h
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hy
    exact congrArg (place chosen) (prior.alone ha hb (by simpa [address] using h))

theorem census (prior:Team R) (chosen:Finset (Leaf R)) (S:StepData c f) :
    (team prior chosen).signs S=prior.signs S :=by
  unfold Team.signs team
  rw [Finset.image_image]
  simp [Function.comp_def,address]

theorem source (prior:Team R) (chosen:Finset (Leaf R)) (atOrdinary:∀v∈chosen,∃i,v.turn=.logKey i)
    (raw:Leaf R → Config G f → ℝ)
    (reading:∀v∈chosen,∀U,v.turn.qualifies R U→v.ingredient U=raw v U)
    {v:Leaf R} (_hv:v∈prior.own) (U:Config G f) :
    v.ingredient U=(if v∈chosen then raw v U else 1)*(place chosen v).ingredient U :=by
  by_cases picked:v∈chosen
  · obtain ⟨i,site⟩:=atOrdinary v picked
    rw [if_pos picked,place,if_pos picked,(regular site U).2]
    by_cases h : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [masked_eq _ _ _ _ h,mul_one]; exact reading _ picked U (by simpa [site,Wing.qualifies] using h)
    · rw [masked_ne _ _ _ _ h,mul_zero]
      by_contra hn; exact h (by simpa [site,Wing.qualifies] using v.grant U hn)
  · rw [if_neg picked,place,if_neg picked,one_mul]

end YM.Integration.WilsonCoherentMayerGate
