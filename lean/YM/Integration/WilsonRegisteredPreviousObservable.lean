import YM.Integration.WilsonRegisteredFrozenReading
import YM.Push.LOCAL_SPLITTING.Direct

/-! The signed original previous row has a bounded Borel gauge-invariant
representative. The bound comes from its original common registered
summable absolute salary, before the covariance is formed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredPreviousObservable
open MeasureTheory Lattice RG Source Wilson Push.Local PhysicalNext.Repeat.Legato
open WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical
variable {G:Gauge} (R:Run G) {m N per d:ℕ}

theorem original (live:m<N) (hr:R.family.ref d ≤ m+1) (w:R.family.label d) (o:Site (R.family.side (m+1) per))
    (b:ℕ) (η:ℂ→L[ℝ]ℝ) :
    Envelope (fun U=>η (previous R live w o b U)) ∧
      GaugeInvariant (fun U=>η (previous R live w o b U)) := by
  let k:=m+1
  let A:=R.family.path.rep N per k
  let Z:=packet R.makes live w o
  let row (i:ℕ)(U:Config G (R.family.side k per)):=if coverNumber A.p.B (Z.support i)<b then Z.maskedTerm A i U else 0
  have prior:=WilsonTranslatedFactory.based R.makes hr live o ((R.family.factory d N per).terminal.symm w)
  have format:Z.Format o R.family.params A:=prior.1
  obtain ⟨B,sB,hB⟩:=Coefficient.regular_series prior.2
  change ∀ i U,‖Z.maskedTerm A i U‖≤B i at hB
  have caps:Dominated row:=by
    refine ⟨B,sB,fun i U=>?_⟩
    by_cases hit:coverNumber A.p.B (Z.support i)<b
    · simpa only [row,hit,if_true] using hB i U
    · simpa only [row,hit,if_false,norm_zero] using (norm_nonneg (Z.maskedTerm A i U)).trans (hB i U)
  have measurable (i:ℕ):Measurable (row i):=by
    by_cases hit:coverNumber A.p.B (Z.support i)<b
    · simp only [row,hit,if_true]
      exact masked_measurable _ _ (Z.regular i) (format.smooth i).borel
    · simp only [row,hit,if_false];exact measurable_const
  obtain ⟨c,hc⟩:=caps.bound
  refine ⟨⟨η.continuous.measurable.comp (Measurable.tsum measurable),‖η‖*c,fun U=>
    (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hc U) (norm_nonneg _))⟩,?_⟩
  intro a U
  apply congrArg η
  change (∑' i,row i (Lattice.gauge a U))=∑' i,row i U
  apply tsum_congr
  intro i
  by_cases hit:coverNumber A.p.B (Z.support i)<b
  · simp only [row,hit,if_true]
    exact Push.Local.Kernel.mask_gauge _ _ (format.smooth i).symmetry a U
  · simp only [row,hit,if_false]

end YM.Integration.WilsonRegisteredPreviousObservable
end
