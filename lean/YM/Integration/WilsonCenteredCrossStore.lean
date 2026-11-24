import YM.Integration.WilsonCenteredCrossFiled
import YM.Integration.WilsonCenteredPaidPublisher

/-! A regular singleton times its actual hard sibling has a literal
one-source coefficient at the capture root, with one hard division. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCrossStore
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Planned.GuardedAtom Push.Local Source Labels
open WilsonCenteredFiledAtoms WilsonCenteredCrossWallet WilsonCenteredCrossFiled
open WilsonCenteredHardFiled WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}

omit [Fintype V] in
theorem original (L : Lamps X ι G P.p o R) (H : Hard X P.p P.activities.forced P.activities.K o R)
    (x : X) (a b : V) (w : V→ℝ) (hw : ∀ i,0<w i) {E κ v σ C Λ δ : ℝ}
    (regular : L.Paid w P.p.B (P.p.supportExponent+2) E) (hard : H.Paid w P.p.B P.p.supportExponent κ)
    (hk : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1) (width : 0≤P.p.supportExponent)
    (law : P.Lawful σ C Λ δ v) (K : Guard.Keeper P.p P.activities) (Z : Support n)
    (y : Site n) (center : y∈Z) (za : o a∈Z) (zb : o b∈Z) (S : SectionData F) (Y : Hol G) :
    let rent:=(Real.exp ((P.p.supportExponent+2)*coverNumber P.p.B Z)*((w a)⁻¹*E))*((w b)⁻¹*κ)
    Store P S Y y κ ((rent+hitWidth P.p*v*rent)/κ)
      (fun U=>(Real.exp (P.exponent U):ℂ)*((L.log x U).part (R.fire a)*(WilsonCenteredAbsoluteHard.gas H x U).part (R.fire b))) := by
  intro rent
  have α : 0≤P.p.supportExponent+2:=by linarith
  obtain ⟨A,count,paid,exactAt⟩ := WilsonCenteredPaidPublisher.original L w hw α regular
  letI : Countable A:=count.to_subtype
  let D:=WilsonCenteredPaidPublisher.keep L A
  have due : D.Paid w P.p.B (P.p.supportExponent+2) E:=paid
  let serial:=docket (Lots D a×Finset ℕ)
  have inv:=fitted D H a b Z K serial w hw α due hard za zb law.labels.forced law.labels.boundK hv room y center x
  obtain ⟨Q,legal,bill,literal⟩:=source S Y y hk _ inv.1 inv.2
  refine ⟨Q,legal,bill,fun U=>?_⟩
  rw [literal]
  change (Real.exp (P.exponent U):ℂ)*WilsonCenteredHardAnswers.read (P:=P) (placed D H a b Z K serial x) U=_
  rw [physical D H a b Z K serial x U inv.2 law.labels.boundK (due.sums α hw x U)
      (Hard.packet_summing _ hard width hw x U),show D.log x U=L.log x U from exactAt x U]

end YM.Integration.WilsonCenteredCrossStore
