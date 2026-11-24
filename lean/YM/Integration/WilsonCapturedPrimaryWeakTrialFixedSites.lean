import YM.Integration.WilsonCapturedPrimaryWeakTrialFixedInput

/-! The same original fine address on every tested coarse lift, including a lift chosen relative to its marker. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialFixedSites
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds WilsonCoeffUV.Winding
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCompactVerseEntrance (CoverBill)
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Carp XSpace
variable {G:Gauge}{n e j:ℕ}{d h:Fin n→ℕ}(R:Run G)
variable (κ:(v:Fin n)→Knob (h v))(pt:Fin n→Chamber)


theorem wrapped {c f L:Side}(A:Ratio c f)(same:A.count=L)(z:Site f)(y:Cover)
    (parent:wrap c y=A.parent z):
    wrap f (L.val • y + lift (same ▸ A.residue z))=z := by
  subst L
  rw [map_add,←A.embed_wrap y,parent]
  exact A.unpack_at z

theorem actual (R:Run G)(Y:Realm G (e+1) Credit.leanC)(course:Y.draws=R.family.path.levels)
    (j per:ℕ):(R.family.S.oneStep j per).count=(ll Y.draws j).L:=by
  rw [course]
  rfl

open WilsonCapturedPrimaryWeakTrialFixedInput (places)

theorem earned (e:ℕ):∃A:ℝ,1≤A ∧ ∀(j per:ℕ)(Y:Realm G (e+1) Credit.leanC)
    (course:Y.draws=R.family.path.levels)(lo:Y.anchor≤j),
    (Y.mint (j+1) (by omega)).σ≤1 →
    ∀(S:Finset (Fin n))(q:(v:Fin n)→Choice R d v)(z:Fin n→Site (R.family.side (j+1) per)),
    let branch:=R.family.S.oneStep j per
    let delta:Fin n→Site (ll Y.draws j).L:=fun v=>actual R Y course j per ▸ branch.residue (z v)
    ∃X:FundedMarkedPathSelection.Input Y lo S d h A,
      X.offsets=(fun _=>delta) ∧
      (∀y,X.familyAt y=start R d κ pt q (places Y (fun _=>delta) y)) ∧
      (∀(N:ℕ) T y,FundedMarkedPathSelection.output X T N y=
        logO Y.draws Y.paid j N (start R d κ pt q (places Y (fun _=>delta) y)) d T) ∧
      ∀(y:Fin n→ Cover),(∀v,wrap (R.family.side j per) (y v)=branch.parent (z v)) →
        ∀v,wrap (R.family.side (j+1) per) (places Y (fun _=>delta) y v)=z v := by
  obtain ⟨A,hA,paid⟩:=WilsonCapturedPrimaryWeakTrialFixedInput.uniform (d:=d) R κ pt e
  refine ⟨A,hA,?_⟩
  intro j per Y course lo width S q z branch delta
  obtain ⟨X,fields,offsets,cash⟩:=paid j Y lo width S q (fun _=>delta)
  exact ⟨X,offsets,congrFun fields,cash,fun y hy v=>wrapped branch (actual R Y course j per) (z v) (y v) (hy v)⟩

end YM.Integration.WilsonCapturedPrimaryWeakTrialFixedSites
