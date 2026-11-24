import YM.Integration.WilsonIndependentPublicFreeTrain
import YM.Integration.WilsonIndependentPublicRawBook

/-! The quadratic subtracted by the Spout and the absence of a bulk linear
action, on the actual clock, level and centered grove of the inversion notebook. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentPublicSpoutGround
open Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue RegulatorIR
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Oracle Next.Free
open Gauge Precision RegulatorIR.Taping
open scoped Classical
variable {G:Gauge}{K:KernelChoices}{W:Type}{M:W→ℕ}{n:Page M→Side}
variable {A:Levels G}{C:Circuit M n}{s:ℕ}{w:W}

theorem actual (R:WilsonIndependentPublicFreeTrain.Matches A C K s w)
    (chart:ChartRatio G)(simple:G.Simple)(locality:LocalRatio chart)
    (Y:Program K)(p:Page M)(hp:p.bindW=w) :
    let N:=s+M w
    let t:=s+(M w-p.downW)
    let H:=(C.tables Y p).diagonal
    (∀ side:Side,(story A chart N t).1 side 0=shine (orbQ (precisionC G side H))) ∧
    actionW A chart N t 0=shine (orbQ (plain G H)) ∧
    (∀ e,actionW A chart N t e 1=0) ∧ Kstar (actionW A chart N t)=1 := by
  dsimp only
  rw [WilsonIndependentPublicFreeTrain.diagonal R Y p hp]
  have ht:s+(M w-p.downW) ≤ s+M w:=by omega
  have cover:=catchment A chart simple locality ht
  have finite:=old A chart simple locality _ _ ht
  exact ⟨fun board=>(finite.basis board).stem,cover.readout,cover.vanishes,cover.rise⟩

theorem blank {S:Heir n G}(V:Reel S)
    (T:S.Accounts)(p:Page M)(r:ℕ):
    T.bulk p 0 r=0 ∧ T.orb p 0 r=0 := by
  constructor
  · by_contra h
    exact (Nat.lt_irrefl 0) ((T.cap_b (fun i=>RegulatorIR.Halo.essential V i) p 0 r h).1)
  · by_contra h
    exact (Nat.lt_irrefl 0) ((T.cap_o (fun i=>RegulatorIR.Halo.essential V i) p 0 r h).1)

end YM.Integration.WilsonIndependentPublicSpoutGround
