import YM.Integration.WilsonReflectedTwoGridFields
import YM.Integration.WilsonReflectedOriginalTwoDeposit
/-! Orient each real field on its own placed source and use the exact
Wilson change of variables at every date of its conditional. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMotionGrid
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p:ℕ}
local notation "C₀" => R.family
local notation "space" i:max => Config G ((C₀).side i p)

private theorem push (i:ℕ)(b:Bool)(s:Signed)(o:Site ((C₀).side i p))(F:space (i+1)→ℂ)
    (h:Integrable F (prior G _)):
    let S:=(C₀).path.levels.clock.op i p
    let β:=(C₀).path.β N p (i+1)
    S.push β (RelayDifference.oriented F b s (S.ratio.embed o))=
      RelayDifference.oriented (S.push β F) b s o:=by
  intro S β
  funext V
  have e:=Motion.push_pull (C₀).path i p β s o F h V
  cases b with
  | false=>exact e
  | true=>
    change S.push β (fun U=>star (F (pull s (S.ratio.embed o) U))) V=star (S.push β F (pull s o V))
    dsimp only at e
    rw [←e]
    unfold StepData.push
    simp_rw [← show ∀ (r:ℝ)(z:ℂ),star (r • z)=r • star z from fun r z=>by rw [star_smul,star_trivial]]
    exact (starL' ℝ (A:=ℂ)).integral_comp_comm _

theorem flowed (b:Bool)(s:Signed)(f:ℕ)(o:Site ((C₀).side f p))(n:ℕ):
    ∀F:space (f+n)→ℂ,Integrable F (prior G _) →
    flow (C₀) 0 N p f n (RelayDifference.oriented F b s (((C₀).S.toDepth (Nat.le_add_right f n) p).embed o))=
      RelayDifference.oriented (flow (C₀) 0 N p f n F) b s o:=by
  induction n with
  | zero=>intro F _;simp only [flow,like_embed]
  | succ n ih=>
    intro F h
    let w:=(C₀).S.toDepth (Nat.le_add_right f n) p
    let r:=((C₀).path.levels.clock.op (f+n) p).ratio
    let v:=(C₀).S.toDepth (Nat.le_add_right f (n+1)) p
    have ink:v.embed o=r.embed (w.embed o):=Next.Rank.Station.embed_comp w r v o
    change flow (C₀) 0 N p f n (transition (C:=C₀) 0 N p (f+n) (RelayDifference.oriented F b s (v.embed o)))=_
    rw [ink,transition,blast,pow_zero,one_smul,push R (f+n) b s (w.embed o) F h]
    let H:=transition (C:=C₀) 0 N p (f+n) F
    have done:=ih H (WilsonOriginalNullCorridor.integrable (C₀) 0 N p h)
    simpa only [H,transition,blast,pow_zero,one_smul,flow] using done

theorem returned {f K:ℕ}(high:K≤N)(before:f≤K)(b:Bool)(s:Signed)(o:Site ((C₀).side f p))
    (F:space K→ℂ)(h:Envelope F)(U:space f):
    actualTransport (C₀) (N:=N) (RelayDifference.oriented F b s (((C₀).S.toDepth before p).embed o)) before U=
      RelayDifference.hand b (actualTransport (C₀) (N:=N) F before (pull s o U)):=by
  obtain ⟨n,rfl⟩:=Nat.exists_eq_add_of_le before
  let E:space (f+n)→ℂ:=fun V=>((C₀).path.rep N p (f+n)).eval V • F V
  let top:=((C₀).S.toDepth before p).embed o
  have inc:Integrable E (prior G _):=ActualWilsonAbsoluteTransport.weighted (C₀) R.makes high h
  have same:(fun V=>((C₀).path.rep N p (f+n)).eval V • RelayDifference.oriented F b s top V)=
      RelayDifference.oriented E b s top:=by
    funext W;rw [RelayDifference.oriented,RelayDifference.oriented]
    have vac:((C₀).path.rep N p (f+n)).eval (pull s top W)=((C₀).path.rep N p (f+n)).eval W:=
      WardBin.Wheels.rep_spins (H:=(C₀).path) s R.makes.wilson high W top
    cases b <;> simp [E,RelayDifference.hand,vac]
  have turn:=congrFun (flowed R (N:=N) b s f o n E inc) U
  simp only [WilsonReceivedQUnitPosterior.raw] at turn
  have one:=actualTransport_unnormalize (C₀) R.makes high (RelayDifference.oriented F b s top) before U
  rw [same,turn] at one
  have two:=actualTransport_unnormalize (C₀) R.makes high F before (pull s o U)
  change _=RelayDifference.hand b (gust (C₀).path N p (f+n) E f before (pull s o U)) at one
  have vac:((C₀).path.rep N p f).eval (pull s o U)=((C₀).path.rep N p f).eval U:=
    WardBin.Wheels.rep_spins (H:=(C₀).path) s R.makes.wilson (before.trans high) U o
  rw [←two,vac] at one
  have pos:0<((C₀).path.rep N p f).eval U:=Multi.AxisShift.chosen_positive R.makes.wilson (before.trans high) U
  cases b <;> simp only [RelayDifference.hand,if_true,if_false,Bool.false_eq_true,star_smul,star_trivial] at one ⊢ <;>
    exact (smul_right_injective ℂ pos.ne' one)

end YM.Integration.WilsonReflectedMotionGrid
end
