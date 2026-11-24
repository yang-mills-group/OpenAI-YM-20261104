import YM.Integration.WilsonIndependentConditionedBankPair

/-! The ordinary independent Gram on the actual fitted columns of one inherited vacancy. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankGram
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentFittedMixedCash (bill embed)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedFittedSeat (dose receiving)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentFittedPivotCash (measured view gross)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
variable {G:Gauge}{k e u₀:ℕ}{H:Hol G}{Q₁ Q₂:SealR G}
    {v₁:Rails Q₁.h k u₀ e}{v₂:Rails Q₂.h k u₀ e}{E W K U:Credit}

open WilsonIndependentConditionedBankPair (Cut)
open WilsonIndependentFittedMixedReturn (planted)
open WilsonIndependentMatchedPivotSeat (axis)
local notation "raw" => WilsonIndependentFittedMixedReturn.word

def weights (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(host:ℕ)(d:Verse Q₁.F)(i:Alma Q₁.F):Cost:=
  clock X.ax X.tx X.N X.m host (d i)

def board (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(Y:CutsP H Q₂.ans Q₂.path v₂ E W K U)
    (host:ℕ)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)(r:ℕ)(z:Fin r→YForest G)
    (i:Alma Q₁.F)(j:Alma Q₂.F):Cost:=
  raw X host (film X i 0 φ y o X.i) (film Y j 0 ψ y o Y.i) r z

theorem fitted (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(Y:CutsP H Q₂.ans Q₂.path v₂ E W K U)
    (levels:Y.ax=X.ax)(prior:Y.tx=X.tx)(vac:Y.N=X.N)(home:Y.m=X.m)(top:Y.ceilC=X.ceilC)
    (host:ℕ)(older:host≤X.m)(a:Verse Q₁.F)(b:Verse Q₂.F)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)
    (y:ℝ)(o:CellR)(r:ℕ)(z:Fin r→YForest G):
    raw X host (planted X a φ y o) (planted Y b ψ y o) r z=
      ∑i,∑j,(weights X host a i*weights Y host b j)*board X Y host φ ψ y o r z i j:=by
  let A:=fun i=>film X i 0 φ y o X.i
  let B:=fun j=>film Y j 0 ψ y o Y.i
  let V:=planted Y b ψ y o
  have left:=(WilsonIndependentFittedPivotRoster.joined X V
    ((WilsonIndependentFittedMixedReturn.paid Y b ψ y o).tall v₂.hk) host older a φ y o r z).2
  rw [left]
  apply sum_congr rfl
  intro i _
  have law(P S:Era G ℝ):raw Y host P S r z=raw X host P S r z:=by
    change WilsonOlderFreshSoftSocketKinetic.reading (cruises Y.ax Y.tx Y.N _ Y.ceilC host (agateV P S)).2 z=
      WilsonOlderFreshSoftSocketKinetic.reading (cruises X.ax X.tx X.N _ X.ceilC host (agateV P S)).2 z
    rw [levels,prior,vac,top]
  have good:Auth k (A i):=(WilsonIndependentFittedMixedReturn.paid X (axis i 0) φ y o).tall v₁.hk
  have right:=(WilsonIndependentFittedPivotRoster.joined Y (A i) good host (home ▸ older) b ψ y o r z).1
  simp only [law] at right
  change weights X host a i*raw X host (A i) V r z=_
  rw [right,mul_sum]
  apply sum_congr rfl
  intro j _
  exact (mul_assoc ..).symm

theorem numerical (X:CutsP H Q₁.ans Q₁.path v₁ E W K U)(Y:CutsP H Q₂.ans Q₂.path v₂ E W K U)
    (levels:Y.ax=X.ax)(prior:Y.tx=X.tx)(vac:Y.N=X.N)(home:Y.m=X.m)(top:Y.ceilC=X.ceilC)
    (host:ℕ)(older:host≤X.m)(a:Verse Q₁.F)(b:Verse Q₂.F)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)
    (y:ℝ)(o:CellR)(r:ℕ)(z:Fin r→YForest G)(q:ℕ)(g:ℝ)(small:|g|≤1):
    let Z:=board X Y host φ ψ y o r z
    let A:=weights X host a
    let B:=weights Y host b
    let evaluated:=fun c:Cost=>measured q g c
    let norm₁:=fun c:Cost=>belt q (embed c)
    let gram:=∑i,∑j,(evaluated (A i)*evaluated (B j))*evaluated (Z i j)
    let annulus:=∑i,∑j,(norm₁ (A i)*norm₁ (B j))*norm₁ (Z i j)
    ‖evaluated (raw X host (planted X a φ y o) (planted Y b ψ y o) r z)-gram‖ ≤
      3*|g|^(q+1)*annulus:=by
  intro Z A B ev norm₁ gram annulus
  dsimp only [gram,annulus,ev]
  rw [fitted X Y levels prior vac home top host older a b φ ψ y o r z,map_sum,←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  rw [map_sum,←sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro j _
  let terms:Fin 3→PowerSeries ℂ:=![embed (A i),embed (B j),embed (Z i j)]
  have one:=WilsonIndependentFittedNumericalProduct.signed q small univ terms
  have t₀:terms 0=embed (A i):=rfl
  have t₁:terms 1=embed (B j):=rfl
  have t₂:terms 2=embed (Z i j):=rfl
  simp only [Fin.prod_univ_three,t₀,t₁,t₂,card_univ,Fintype.card_fin] at one
  change ‖cash q g (embed ((A i*B j)*Z i j))-
    ((cash q g (embed (A i))*cash q g (embed (B j)))*cash q g (embed (Z i j)))‖ ≤ _
  simp only [map_mul]
  rw [norm_sub_rev]
  simpa only [norm₁,Nat.cast_ofNat,mul_assoc] using one

end YM.Integration.WilsonIndependentConditionedBankGram
