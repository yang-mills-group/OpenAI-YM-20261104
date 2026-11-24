import YM.Integration.WilsonIndependentMovingRosterAllFineSeats
import YM.Integration.WilsonIndependentCutJoinPlate

/-! Simultaneous canonical marked passports and receiver costs on the public
two-length inversion board, with the selected heat calendar and optical gap. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFinePlate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old)
open RegulatorIR RegulatorIR.Ledger
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{e height seats j extra:ℕ}
open WilsonIndependentMovingRosterAllFineSeats (Elected)

theorem original (R:Master H)(chart:ChartRatio G)(kernel:KernelChoices)(V:XSpace.Run)
    (B:WilsonIndependentEvenPassport.Menu R chart kernel V e height seats j extra)
    (grant:WilsonIndependentCutJoinPlate.Approved R chart kernel V e height seats j extra B)
    (phase:4 ≤ j)(i:Requests B.a):
    let cir:=WilsonIndependentExactPlate.S V B.a B.positive j phase
    let N:=WilsonIndependentExactPlate.M V B.a i
    let r:Fin B.a:=⟨i.val%B.a,Nat.mod_lt _ B.positive⟩
    ∃(A:Levels G)(s:ℕ),A.clock.kernel=kernel ∧
      (∀p:Page (WilsonIndependentExactPlate.M V B.a),p.bindW=i→A.clock.J (s+(N-p.downW))=cir.J p) ∧
      (∀f:Flap (WilsonIndependentExactPlate.M V B.a),f.volW=i→∀per:ℕ,
        (A.clock.op (s+(N-(f.offset+1))) per).patch=cir.pactP f) ∧
      A.S.scale (s+N)-A.S.scale (s+old V B.a i.val)= -Real.log (V.step i.val).spacing ∧
      ∀(h D:ℕ)(p:h<D),h ≤ height→D ≤ seats→
      ∃W:ChorusLine H (R.T h) p e C C C,
        W.arch.V.draws=A ∧ W.arch.V.paid=chart ∧ W.arch.V.y=extendedY (B.price r) A.S (s+N) ∧
        W.arch.V.anchor=s ∧ (∀z ≤ N,W.arch.V.y (s+z)=B.price r) ∧ Weston W.arch C ∧
        (∀age (engaged:W.arch.V.anchor ≤ age),∃a:5 ≤ A.clock.J (age+1),
          (W.arch.angle age engaged).lamp.exitS=crestM A age a) ∧
        (∀(k u:ℕ)(v:Rails h k u e),k ≤ seats→u ≤ seats→∃L:Torch H (R.T h) p v C C C,L.L=W.arch) ∧
        Elected R W.arch.V height seats:=by
  intro cir N r
  obtain ⟨A,s,ker,stages,patches,dist,money,all⟩:=WilsonIndependentCutJoinPlate.optics
    R chart kernel V e height seats j extra B grant phase i
  refine ⟨A,s,ker,stages,patches,dist,?_⟩
  intro h D p grade dim
  obtain ⟨W,draw,quiet,tariff,anchor,west,lamps,torches,rates⟩:=all h D p grade dim
  refine ⟨W,draw,quiet,tariff,anchor,?_,west,lamps,torches,?_⟩
  · rw [tariff]
    exact money
  · exact WilsonIndependentMovingRosterAllFineSeats.original R A chart _ s all W.arch.V draw quiet tariff anchor rates

end YM.Integration.WilsonIndependentMovingRosterAllFinePlate
