import YM.Integration.WilsonLocalAnchoredKernel

/-! The complement of a local cut costs the original conditional absolute
moment of the same signed spectator, with the same relative kernel bound. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHeldRough
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision
open PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G:Gauge}

theorem original (R:Run G) {N per m:ℕ} (live:m<N) (V:Config G (R.family.side m per))
    (D H:Config G (R.family.side (m+1) per)→ℝ) {C:Set (Config G (R.family.side (m+1) per))}
    (ms:MeasurableSet C) {L:ℝ} (mD:Measurable D) (env:Envelope H)
    (paid:∀U,|D U|≤L*actualConditionalDensity R.family N per m V U) :
    let h:=fun U=>D U*H U
    let ν:=prior G (R.family.side (m+1) per)
    |(∫U,h U ∂ν)-(∫U,C.indicator h U ∂ν)| ≤ L*actualAverage R.family (N:=N) (Cᶜ.indicator (fun U=>|H U|)) V := by
  intro h ν
  let ρ:=actualConditionalDensity R.family N per m V
  have ew:=WilsonCoherentMeasuredChart.driver R m per N live V
  have eH:Envelope (fun U=>|H U|):=⟨env.meas.abs,env.cost.imp fun _ h U=>by simpa only [Real.norm_eq_abs,abs_abs] using h U⟩
  have cap (U):‖h U‖≤L*(ρ U*|H U|) := by
    rw [show h U=D U*H U from rfl,Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_right (paid U) (abs_nonneg _)).trans_eq (by ring)
  have ih:Integrable h ν:=(((ew.mul eH).integrable ν).const_mul L).mono' (mD.mul env.meas).aestronglyMeasurable (ae_of_all _ cap)
  have split:(∫U,h U ∂ν)=(∫U,C.indicator h U ∂ν)+(∫U,Cᶜ.indicator h U ∂ν):=by
    rw [←integral_add (ih.indicator ms) (ih.indicator ms.compl)]
    apply integral_congr_ae;apply ae_of_all;intro U
    by_cases mem:U∈C <;> simp [mem]
  rw [split,add_sub_cancel_left]
  let k:=fun U=>ρ U*Cᶜ.indicator (fun U=>|H U|) U
  have ik:Integrable k ν:=by
    have eq:k=Cᶜ.indicator (fun U=>ρ U*|H U|):=funext fun U=>by
      by_cases hit:U∈Cᶜ
      · simp only [k,indicator_of_mem hit]
      · simp only [k,indicator_of_notMem hit,mul_zero]
    rw [eq];exact ((ew.mul eH).integrable ν).indicator ms.compl
  have cost (U):‖Cᶜ.indicator h U‖≤L*k U:=by
    by_cases mem:U∈Cᶜ
    · simp only [k,indicator_of_mem mem];exact cap U
    · simp only [k,indicator_of_notMem mem,mul_zero,norm_zero,le_refl]
  have price:=norm_integral_le_of_norm_le (ik.const_mul L) (ae_of_all _ cost)
  rw [Real.norm_eq_abs,integral_const_mul] at price
  exact price

end YM.Integration.WilsonLocalHeldRough
