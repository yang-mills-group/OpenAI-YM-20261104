import YM.Integration.WilsonIndependentSpoutMasterWords

/-! The ordinary normalized source at the marked birth on its actual older vacuum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterArms
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Source Source.Drops Labels
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonMarkedIndependentNormalizedElection (normalized)
open scoped BigOperators Classical
variable {G:Gauge}{n e:ℕ}(L:Levels G)(O:ChartRatio G)

def arm (Q:SealR G)(φ:Rarity Q.D)(b:Q.Rider)(m K N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  word (Shrine (Peaks L O Q.ans Q.path N K) (received L O Q m K N b)) φ (paceT L.S m K) y o Q.h

theorem opened (Q:SealR G)(φ:Rarity Q.D)(b:Q.Rider)(m K N:ℕ)(y:ℝ)(o:CellR):
    arm L O Q φ b m K N y o=
      ∑a,affiled (reel (relativeC L O N m (K-m)) (b a)) (arm L O Q φ (axis Q a) m K N y o):=by
  let α:=reel (relativeC L O N m (K-m))
  let basis a:=received L O Q m K N (axis Q a)
  have face:received L O Q m K N b=fun j=>∑a,α (b a)*basis a j:=
    funext (WilsonIndependentSpoutMasterCoordinates.original L O Q N m K b)
  unfold arm
  rw [face,WilsonIndependentSpoutMasterWords.shrine]
  exact WilsonIndependentSpoutMasterWords.profile _ _ φ _ y o _ (pace_pos ..)

theorem licensed (Q:SealR G){H:Hol G}{P W:Credit}(F:Theatre H Q.ans Q.path e P W)
    (φ:Rarity Q.D)(b:Q.Rider)(m K N:ℕ)(awake:F.V.anchor ≤ K)(top:K ≤ N)(y:ℝ)(o:CellR):
    Auth Q.h (arm F.V.draws F.V.paid Q φ b m K N y o):=
  locale_val _ (Mer.placed Q.h φ (Shrine_on _ (production F top awake).1 _ le_rfl) _ y) o

def basis (Q:Fin (n+1)→SealR G)(a:∀i,Alma (Q i).F):Herit Q:=
  fun i=>axis (Q i) (a i)

theorem original (Q:Fin (n+1)→SealR G)(φ:Wilt Q)(b:Herit Q)(m K N:ℕ)(y:ℝ)(o:CellR)
    (paid:∀i a,Auth (Q i).h (arm L O (Q i) (φ i) (axis (Q i) a) m K N y o)):
    Ashore Q L O φ (normalized L O Q b m N) m K N y o =
       ∑a:(∀i,Alma (Q i).F),affiled (reel (relativeC L O N m (K-m)) (∏i,b i (a i)))
          (Ashore Q L O φ (normalized L O Q (basis Q a) m N) m K N y o):=by
  let A:=(reel (relativeC L O N m (K-m)))
  let arms i (a:Alma (Q i).F):=arm L O (Q i) (φ i) (axis (Q i) a) m K N y o
  let source i (a:Alma (Q i).F):=affiled (A (b i a)) (arms i a)
  have live i a:Auth (Q i).h (source i a):=WilsonIndependentMatchedOpeningFee.grant _ (paid i a) _
  change MassP G ℝ n (fun i=>arm L O (Q i) (φ i) (b i) m K N y o)=_
  have swap: (fun i=>arm L O (Q i) (φ i) (b i) m K N y o)=fun i=>∑a,source i a:=
    funext fun i=>opened L O (Q i) (φ i) (b i) m K N y o
  rw [swap,WilsonIndependentMatchedOpeningMass.original _ (fun i=>(Q i).h) source live]
  apply Finset.sum_congr rfl
  intro a _
  change MassP G ℝ n (fun i=>affiled (A (b i (a i))) (arms i (a i)))=
    affiled (A (∏i,b i (a i))) (MassP G ℝ n (fun i=>arms i (a i)))
  rw [map_prod]
  exact WilsonIndependentMatchedOpeningFee.risk _ (fun i=>(Q i).h) (fun i=>paid i (a i)) _
end YM.Integration.WilsonIndependentSpoutMasterArms
end
