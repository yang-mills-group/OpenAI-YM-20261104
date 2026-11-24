import YM.Integration.WilsonCapturedMountedColorIncome
import YM.Integration.WilsonMeasuredOriginalPeriodWord
import YM.Integration.WilsonOriginalMarkedFaceReading

/-! The appointed page at the original period carries the complete
occupied group word at every compact field. Its real projections preserve
the physical marked bank's regularity, gauge invariance and envelope. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingMaterial
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe
open Comparison.RG02 Multi Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonCapturedPinnedGroupClock WilsonCapturedPinnedColorFile WilsonOriginalOccupiedFieldLayout
open WilsonOriginalPaidWalkCover
open WilsonOriginalPolarizedAngularPage WilsonOriginalLinkedAngularPage WilsonOriginalMarkedFaceReading
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}

private theorem samePage (n:Side)(u b:Fin (Pages n n)):u=b:=by
  have count:Pages n n=1:=by simp [Pages,Nat.div_self n.pos]
  apply Fin.ext
  have hu:=u.isLt
  have hb:=b.isLt
  omega

theorem own (o:Site n)(f:Stationary.Link G n→ℂ) :
    board (n:=n) dvd_rfl o (move G) f = f:=by
  classical
  let b:Fin (Pages n n):=⟨0,by simp [Pages,Nat.div_self n.pos]⟩
  funext A
  rw [board,Finset.sum_apply,Finset.sum_eq_single b]
  · change f (move G ((page dvd_rfl (splitter dvd_rfl o) b).val-o) A)=f A
    rw [WilsonMeasuredOriginalPeriodRead.atSite,WilsonMeasuredOriginalPeriodRead.identity,sub_self]
    apply congrArg f
    funext i
    simp [move]
  · intro u _ ne
    exact (ne (samePage n u b)).elim
  · simp

variable (M:ι→Row o J G X) (t:X)(grade:V→ℕ) (layout:Layout G) (tape:Finset Age)
local notation "physical" => Air.craft M (fun i=>(M i).paint t) grade layout tape

theorem material (s:Hot J) (v:s.val.val) (b:Fin (Pages n n)) :
    ink dvd_rfl M t s.val v b ((physical).power s) (physical).vac =
      field physical s (Stock.census Unit):=by
  classical
  unfold ink field
  congr 1
  funext _ g U
  unfold group Air.craft Fk.grant Air.sums
  apply tsum_congr
  intro i
  rw [Finset.sum_eq_single b]
  · have pin:=samePage n (index dvd_rfl (M i) b v.val) b
    simp only [pin,and_true]
    unfold ScatterR.actor ScatterR.familyAt
    by_cases yes:(M i).mode=s.val
    · simp only [yes,if_true]
      rw [WilsonOriginalPaidWalkCover.centered,anchor,WilsonMeasuredOriginalPeriodRead.atSite]
      rfl
    · simp [yes]
  · intro u _ ne
    exact (ne (samePage n u b)).elim
  · simp

theorem legal {Λ:Type}[DecidableEq Λ]{K:Census Λ}(Z:Bulk.Colors K G n)(well:Bulk.Well Z)
    (L:ℂ→L[ℝ]ℝ):Bulk.Well (channel L Z):=by
  let E:=Complex.ofRealCLM ∘L L
  refine ⟨well.suppose_vac,fun i=>Assembly.GradeAt.linear_contact E (well.suppose_mark i),
    well.natural,?_,well.envelope,?_⟩
  · intro i θ h U
    exact congrArg E (well.gauges i θ h U)
  · intro i θ
    obtain ⟨K,cap⟩:=(well.prices i θ).cost
    exact ⟨E.continuous.measurable.comp (well.prices i θ).meas,‖E‖*K,
      fun U=>(E.le_opNorm _).trans (mul_le_mul_of_nonneg_left (cap U) (norm_nonneg _))⟩

end YM.Integration.WilsonCapturedPrimaryWindingMaterial
