import YM.Integration.WilsonOriginalMeasuredBoxResidual

/-! At either boundary of the real period the measured compact window and
every one of its derivatives agree with their actual periodic extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPeriodicWindowGerm
open Set Filter AddCircle
open scoped Topology

theorem germ {a l h x : ℝ} (f : ℝ → ℂ) (left : a < l) (right : h < a+1)
    (outside : ∀ t, t ∉ Icc l h → f t = 0) (hx : x ∈ Icc a (a+1)) :
    (fun t : ℝ => AddCircle.liftIoc (1:ℝ) a f (t:UnitAddCircle)) =ᶠ[𝓝 x] f := by
  have lo := hx.1
  have hi := hx.2
  filter_upwards [lt_mem_nhds (show h-1 < x by linarith),
    lt_mem_nhds (show a-1 < x by linarith),gt_mem_nhds (show x < l+1 by linarith),
    gt_mem_nhds (show x < a+2 by linarith)] with t ht hw hu hv
  by_cases before : t ≤ a
  · have moved : t+1 ∈ Ioc a (a+1) := ⟨by linarith,by linarith⟩
    have eq := AddCircle.liftIoc_coe_apply (p:= (1:ℝ)) (f:=f) moved
    rw [AddCircle.coe_add_period] at eq
    rw [eq,outside _ (fun g => (show h < t+1 by linarith).not_ge g.2),
      outside _ (fun g => (before.trans_lt left).not_ge g.1)]
  · by_cases inside : t ≤ a+1
    · exact AddCircle.liftIoc_coe_apply ⟨not_le.mp before,inside⟩
    · have moved : t-1 ∈ Ioc a (a+1) := ⟨by linarith [not_le.mp inside],by linarith⟩
      have eq := AddCircle.liftIoc_coe_apply (p:=(1:ℝ)) (f:=f) moved
      have same : ((t-1 : ℝ):UnitAddCircle) = (t:UnitAddCircle) := by
        have e := AddCircle.coe_add_period (1:ℝ) (t-1)
        simpa only [sub_add_cancel] using e.symm
      rw [same] at eq
      rw [eq,outside _ (fun g => (show t-1 < l by linarith).not_ge g.1),
        outside _ (fun g => (right.trans (not_le.mp inside)).not_ge g.2)]

theorem original {a l h x : ℝ} (f : ℝ → ℂ) (left : a < l) (right : h < a+1)
    (outside : ∀ t, t ∉ Icc l h → f t = 0) (hx : x ∈ Icc a (a+1)) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => AddCircle.liftIoc (1:ℝ) a f (t:UnitAddCircle)) x =
      iteratedDeriv n f x :=
  (germ f left right outside hx).iteratedDeriv_eq n

end YM.Integration.WilsonOriginalPeriodicWindowGerm
