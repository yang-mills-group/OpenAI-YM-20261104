import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFundedRegularWindow
import YM.Integration.FVA1Physical.Marked.VacuumHitSlice
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected

/-! The first weak-action insertion on a physical fibre. All regular
activities disjoint from the varied collar disappear under covariance. The
long part incident to the collar is paid with the true support exponent and
the entire physical exterior remains available as a signed spectator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG Wilson RoseCut.FiledAction Marked.Inherited
open scoped Classical BigOperators
open private agreed from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFundedRegularWindow
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def shortRegular (A:Activities G n)(p:BudgetPoint)(L:Support n)(cut:ℕ)(U:Fld):ℝ:=
  sliceLog A p (halo 8 L) 0 U-sliceLog A p (halo 8 L) cut U

/-- The full original regular action increment minus the short incident
increment is exactly the increment of the far incident slice, including
the original healthy/failure mask for every regular occurrence. -/
theorem original_short_increment (A:Activities G n)(p:BudgetPoint){ε ζ:ℝ}(pay:A.Valid p ε ζ)
    (width:1≤p.supportExponent)(L:Support n)(cut:ℕ)(U V:Fld)(keep:Kept U V L):
    (A.additive p U-A.additive p V)-(shortRegular A p L cut U-shortRegular A p L cut V)=
      sliceLog A p (halo 8 L) cut U - sliceLog A p (halo 8 L) cut V ∧
    |(A.additive p U-A.additive p V)-(shortRegular A p L cut U-shortRegular A p L cut V)|≤
       2*sliceFare p (halo 8 L) cut ε:=by
  let Z:=halo 8 L
  have ss(W:Fld):Summable (fun i=>sliceRow A p Z 0 i W):=
    (hit_slice_rows A p pay.boundE width Z 0 (fun _=>W)).2.1.of_norm
  have eq:A.additive p U-A.additive p V=sliceLog A p Z 0 U-sliceLog A p Z 0 V:=by
    unfold Activities.additive sliceLog
    rw [←Summable.tsum_sub ((Activities.ESeries pay).summable U) ((Activities.ESeries pay).summable V),
      ←Summable.tsum_sub (ss U) (ss V)]
    apply tsum_congr;intro i
    by_cases reached:incident A p Z 0 i
    · simp only [sliceRow,if_pos reached]
    have apart:Disjoint Z (A.reg i).support:=by
      apply Finset.disjoint_left.mpr;intro y hy inside
      exact reached ⟨⟨y,hy,inside⟩,Nat.zero_le _⟩
    rw [agreed p keep (pay.regular.smooth i) apart]
    simp only [sliceRow,if_neg reached,sub_self]
  have sharp:(A.additive p U-A.additive p V)-(shortRegular A p L cut U-shortRegular A p L cut V)=
      sliceLog A p Z cut U - sliceLog A p Z cut V:=by
    rw [eq];unfold shortRegular;dsimp only [Z];ring
  refine ⟨sharp,?_⟩;rw [sharp]
  have cap:=(hit_slice_log A p pay.boundE pay.regular width Z cut).2
  exact (abs_sub _ _).trans (by simpa only [two_mul,Real.norm_eq_abs,Z] using add_le_add (cap U) (cap V))

/-- The tested first insertion, with its conditional reference value
retained until after centering the near field. -/
def firstRead {X:Type*}[MeasurableSpace X](ν:Measure X)(f:X→ℝ)(D:X→ℝ):ℝ:=
  ∫x,(f x-∫y,f y ∂ν)*D x ∂ν

private theorem subenv {Y:Type*}[MeasurableSpace Y]{a b:Y→ℝ}(ea:Envelope a)(eb:Envelope b):
    Envelope (fun y=>a y-b y):=by simpa only [sub_eq_add_neg] using ea.add eb.neg

theorem paid_conditional_insertion {X:Type*}[MeasurableSpace X](ν:Measure X)[IsProbabilityMeasure ν]
    (A:Activities G n)(p:BudgetPoint){ε ζ:ℝ}(pay:A.Valid p ε ζ)(width:1≤p.supportExponent)
    (L:Support n)(cut:ℕ)(J:X→Fld)(jm:Measurable J)(V:Fld)(kept:∀x,Kept (J x) V L)
    (f:X→ℝ)(fe:Envelope f):
    let D:=fun x=>A.additive p (J x)-A.additive p V
    let B:=fun x=>shortRegular A p L cut (J x)-shortRegular A p L cut V
    |firstRead ν f D - firstRead ν f B| ≤
      (2*sliceFare p (halo 8 L) cut ε)*(∫x,|f x-∫y,f y ∂ν| ∂ν):=by
  intro D B
  let Z:=halo 8 L
  have cap0:=hit_slice_log A p pay.boundE pay.regular width Z 0
  have capd:=hit_slice_log A p pay.boundE pay.regular width Z cut
  have long:Envelope (sliceLog A p Z cut):=⟨capd.1,_,capd.2⟩
  have all:Envelope (sliceLog A p Z 0):=⟨cap0.1,_,cap0.2⟩
  have whole:Envelope (A.additive p):=⟨A.E_measurable pay.regular,(Activities.ESeries pay).bound⟩
  have pull {h:Fld→ℝ}(he:Envelope h):Envelope (fun x=>h (J x)):=by
    obtain ⟨c,cb⟩:=he.cost;exact ⟨he.meas.comp jm,c,fun x=>cb _⟩
  have De:Envelope D:=subenv (pull whole) (Envelope.const _)
  have Be:Envelope B:=subenv (pull (subenv all long)) (Envelope.const _)
  let F:=fun x=>f x-∫y,f y ∂ν
  have ef:Envelope F:=subenv fe (Envelope.const _)
  have exactDiff:firstRead ν f D-firstRead ν f B=∫x,F x*(D x-B x) ∂ν:=by
    unfold firstRead
    rw [←integral_sub ((ef.mul De).integrable ν) ((ef.mul Be).integrable ν)]
    apply integral_congr_ae;filter_upwards with x;dsimp only [F];ring
  rw [exactDiff,←integral_const_mul]
  apply (norm_integral_le_of_norm_le (f:=fun x=>F x*(D x-B x))
      ((ef.integrable ν).norm.const_mul (2*sliceFare p Z cut ε)) ?_)
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_mul,mul_comm (2*sliceFare p Z cut ε)]
  exact mul_le_mul_of_nonneg_left (original_short_increment A p pay width L cut (J x) V (kept x)).2 (abs_nonneg _)

end YM.Integration.FVA1Physical.Exchange.F6Regular
