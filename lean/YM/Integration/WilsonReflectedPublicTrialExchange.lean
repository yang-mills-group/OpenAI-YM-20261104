import YM.Integration.WilsonReflectedPublicGuardedEstate
import YM.Integration.WilsonReflectedPublicTrialTuition
import YM.Integration.WilsonMeasuredPublicEntranceCheapField
/-! The ordered comparison on a reflected pair of original courses uses the
actual guarded coordinate of each measured input. The signed regular source
and its two separate hard inventories stay on their respective physical hosts. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicTrialExchange
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion Marker
open RG05Readout RG05Readout.Address MergeProof Extra.Multi Trace.Physical Trace.Physical.Germ
open Push PhysicalNext.Repeat.Legato QuadraticLocal.Affinity WilsonReflectedFundedHearing
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceCheapOrder
open WilsonMeasuredPublicEntranceCheapField WilsonReflectedPublicTrialRoster
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p f K:ℕ}{I:Type}[DecidableEq I][Fintype I]
    (d:I→ℕ)(A:(v:I)→Arm R (d v) N p f K)(h:f≤K)(high:K≤N)(dose:I→ℂ)
local notation "C₀" => R.family
local notation "PF" => (C₀).path.rep N p f
local notation "seat" => fun v=>(A v).o
local notation "native" => WilsonOriginalAlternativeTrialSource.arm R d N p K (root R d A h) (weight R d A) (factor R K d dose)

include high in
omit [DecidableEq I][Fintype I] in
theorem actual (i:I)(U:Config G ((C₀).side f p)):
    actualTransport (C₀) (N:=N) (native i) h U=
      dose i * WilsonReflectedRestartedPair.mean R N (cropped R (A i) h) f U:=by
  have eq:(native i)=dose i • cropped R (A i) h:=by
    funext W
    exact WilsonReflectedPublicTrialRoster.original R d A h dose i W
  have env:=WilsonReflectedPlacedArm.trial_paid (N:=N) R (d i) h (A i).w (A i).b (A i).s (A i).o
  rw [eq,WilsonReflectedRestartedPair.mean,dif_pos h]
  exact WilsonReflectedPlacedArm.linear R high h (cropped R (A i) h) env (dose i) U

variable (row:I→Three G (R.family.side f p))(wallet head savings:I→ℝ)
    (X E Y:(v:I) → Coefficient (R.family.labels.level (d v)) (R.family.side f p))
    (W:Rep G (R.family.side f p))(b:I → Config G (R.family.side f p)→ℂ)
local notation "filed_" v:max => (Y v).density ((A v).o) ((C₀).localSection (d v)) W
local notation "part_" v:max => (X v).density ((A v).o) ((C₀).localSection (d v)) (PF)
local notation "delta_" v:max => (E v).density ((A v).o) ((C₀).localSection (d v)) (PF)

omit [DecidableEq I][Fintype I] in
theorem sheet (same:W.eval=(PF).eval) (i:I)
    (owned:WilsonReflectedPublicGuardedColumns.Joined R (A i) h high (dose i) (row i)
      (wallet i) (head i) (savings i) (X i) (E i)) (U:Config G (R.family.side f p))
    (trial:(filed_ i) U/(W.eval U:ℂ)=actualTransport (C₀) (N:=N) (native i) h U-b i U):
    (part_ i) U-(delta_ i) U=((PF).eval U:ℂ)*b i U+(filed_ i) U:=by
  have D:((PF).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (h.trans high) U).ne'
  rw [same,actual R d A h high dose] at trial
  rw [owned.arrived,owned.difference.field,(div_eq_iff D).mp trial]
  ring

omit [DecidableEq I][Fintype I] in
theorem one (i:I)(U:Config G (R.family.side f p))
    (empty:(Y i).x=0 ∧ (Y i).regular=0)
    (bank:(part_ i) U-(delta_ i) U=((PF).eval U:ℂ)*b i U+(filed_ i) U):
    ((PF).eval U:ℂ)*(b i U-((X i).exponentialEntry ((A i).o) ((C₀).localSection (d i)) (PF) U-
      (E i).exponentialEntry ((A i).o) ((C₀).localSection (d i)) (PF) U))=
      account (X i) (PF) U-account (Y i) W U-account (E i) (PF) U:=by
  have zero:(Y i).exponentialEntry ((A i).o) ((C₀).localSection (d i)) W U=0:=by
    simp [Coefficient.exponentialEntry,Coefficient.maskedTerm,empty.1,empty.2,masked,SectionData.places,SectionData.evaluate]
  simp only [Coefficient.density,account,zero,mul_zero,zero_add] at bank ⊢
  linear_combination -bank

omit [DecidableEq I][Fintype I] in
theorem original (same:W.eval=(PF).eval)
    (owned:∀v,WilsonReflectedPublicGuardedColumns.Joined R (A v) h high (dose v) (row v)
      (wallet v) (head v) (savings v) (X v) (E v))
    (empty:∀v,(Y v).x=0 ∧ (Y v).regular=0)
    (trial:∀v U,(filed_ v) U/(W.eval U:ℂ)=actualTransport (C₀) (N:=N) (native v) h U-b v U)
    (vs:List I)(U:Config G (R.family.side f p)):
    let x:=fun v=>regular R d (PF) (fun i=>(A i).o) X v U
    let e:=fun v=>regular R d (PF) (fun i=>(A i).o) E v U
    let y:=fun v=>b v U
    let hard:=fun v=>account (X v) (PF) U-account (Y v) W U-account (E v) (PF) U
    ((PF).eval U:ℂ)*((vs.map x).prod-(vs.map y).prod)=
      ((PF).eval U:ℂ)*route x (fun v=>x v-e v) e vs-route y (fun v=>x v-e v) hard vs:=by
  apply WilsonMeasuredPublicEntranceCheapOrder.original
  intro i
  exact one R d A X E Y W b i U (empty i)
    (sheet R d A h high dose row wallet head savings X E Y W b same i (owned i) U (trial i U))

end YM.Integration.WilsonReflectedPublicTrialExchange
end
