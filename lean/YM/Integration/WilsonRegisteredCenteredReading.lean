import YM.Integration.WilsonRegisteredFrozenConditional
import YM.Integration.WilsonRegisteredDegreeFourCovariance

/-! The authentic marginal of each separately submitted grade-four field.
The corrected reading keeps its whole forced gas and its own true mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredCenteredReading
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open Pert.Asymptotics WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonInheritedRegisteredField WilsonRegisteredAffineSource WilsonReportingForestAngularFare
open private real_test from YM.Integration.WilsonRegisteredDegreeFourCovariance
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {m N per:ℕ}
local notation "A" => R.family.path
local notation "n" => R.family.side (m+1) per
local notation "c" => R.family.side m per

def source (live:m+1≤N) (v:R.family.label 4) (o:Site n) (η:ℂ→L[ℝ]ℝ) (U:Config G n) : ℝ :=
  η (field R.makes live v o U)

def centered (live:m+1≤N) (v:R.family.label 4) (o:Site n) (η:ℂ→L[ℝ]ℝ) (V:Config G c) (U:Config G n) : ℝ :=
  source R live v o η U-actualAverage R.family (N:=N) (source R live v o η) V

theorem observable (live:m+1≤N) (ref:R.family.ref 4 ≤ m+1) (v:R.family.label 4)
    (o:Site n) (η:ℂ→L[ℝ]ℝ) (V:Config G c) :
    Envelope (centered R live v o η V) ∧ GaugeInvariant (centered R live v o η V) := by
  have registered:=WilsonMeasuredInheritedGauge.occupied R.family R.makes live v ((R.family.S.toDepth live per).embed o)
  dsimp only at registered
  rw [WilsonInheritedRegisteredField.original (C:=R.family) R.makes live ref v o] at registered
  have e:Envelope (source R live v o η):=real_test registered.1 η
  refine ⟨?_,fun a U=>congrArg (fun z=>η z-actualAverage R.family (N:=N) (source R live v o η) V) (registered.2 a U)⟩
  change Envelope (fun U=>source R live v o η U-actualAverage R.family (N:=N) (source R live v o η) V)
  simpa only [sub_eq_add_neg] using e.add (Envelope.const (-actualAverage R.family (N:=N) (source R live v o η) V))

def amplitude (m:ℕ) : ℝ := (R.family.S.a (m+1))⁻¹^4

def fare (live:m+1≤N) (v:R.family.label 4) (o:Site n) (q:ℕ) (η:ℂ→L[ℝ]ℝ) : ℝ :=
  let Z:=packet R.makes live v o
  amplitude R m*(‖η‖*((R.family.path.levels.params (m+1)).columns*(R.family.labels.level 4).coeffSize
      ((R.family.labels.level 4).core Z.x)*(width R N per (m+1)^(q+1)/q.factorial)))

def filed (live:m+1≤N) (v:R.family.label 4) (o:Site n) (b q:ℕ) (T:Forest ((A).levels.clock.op m per).ratio) (B:Finset T.Free)
    (η:ℂ→L[ℝ]ℝ) (V:Config G c) (z:Sample T B G):ℝ :=
  centered R live v o η V (state T B z)-amplitude R m*
    (η (WilsonRegisteredFrozenReading.previous R live v o b (state T B z))-WilsonRegisteredFrozenReading.reading R live v o b q T B η z)

theorem measurable (live:m+1≤N) (ref:R.family.ref 4 ≤ m+1) (v:R.family.label 4)
    (o:Site n) (b q:ℕ) (T:Forest ((A).levels.clock.op m per).ratio) (B:Finset T.Free) (η:ℂ→L[ℝ]ℝ) (V:Config G c) :
    Measurable (filed R live v o b q T B η V) := by
  have e:=WilsonRegisteredPreviousObservable.original R live ref v o b η
  exact (((observable R live ref v o η V).1.meas).comp (measurable_state T B)).sub
    (((e.1.meas.comp (measurable_state T B)).sub (WilsonRegisteredFrozenReading.measured R live v o b q T B η ref)).const_mul _)

theorem paid (simple:G.Simple) :
    ∀ᶠ m:ℕ in atTop,∀N per (live:m+1≤N) (_ref:R.family.ref 4 ≤ m+1) (v:R.family.label 4) (o:Site (R.family.side (m+1) per))
    (b H q:ℕ) (T:Forest ((A).levels.clock.op m per).ratio) (B:Finset T.Free) (η:ℂ→L[ℝ]ℝ)
    (V:Config G (R.family.side m per)) (z:Sample T B G),
    let k:=m+1
    let Q:=(A).rep N per k
    b*(4*Q.p.B+2)+2*Q.p.B≤H→
    ‖z.2‖≤regulatorRun R.family N per k*((Real.log ((A).levels.clock.hatBeta k))^2/32)→q+1≤Q.p.order→
    state T B z∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut ((A).levels.clock.hatBeta k))→
    |centered R live v o η V (state T B z)-filed R live v o b q T B η V z|≤fare R live v o q η := by
  filter_upwards [WilsonRegisteredFrozenReading.original R simple] with m bound N per live ref v o b H q T B η V z k Q range small active inside
  have step:=bound N per live 4 ref v o b H q T B η z range small active inside
  have positive:0≤amplitude R m:=by unfold amplitude;positivity [R.family.S.a_pos (m+1)]
  simpa only [filed,sub_sub_cancel,abs_mul,abs_of_nonneg positive,fare] using mul_le_mul_of_nonneg_left step positive

end YM.Integration.WilsonRegisteredCenteredReading
end
