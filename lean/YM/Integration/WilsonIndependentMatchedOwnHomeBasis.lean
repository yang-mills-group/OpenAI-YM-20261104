import YM.Integration.WilsonIndependentMatchedOwnHomeRoster
import YM.Integration.WilsonSeparatedPrefixMovingPairSector

/-! Expand in the one actual measured coordinate at the near reporter, and
hear each normalized basis field on its personal home before any covariance. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOwnHomeBasis
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonIndependentSpoutMasterArms (arm basis)
open WilsonIndependentMatchedOwnHomeCoordinates (brought)
open WilsonIndependentMatchedOwnHomeProfile (scaled)
open WilsonIndependentMatchedOwnHomeRoster (away)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonMarkedIndependentNormalizedElection (normalized)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{n e:ℕ}{U W V:Credit}

def asking (R:Realm G (e+1) U)(Q:SealR G)(φ:Rarity Q.D)(b:Q.Rider)(t m K N:ℕ)(y:ℝ)(o:CellR):Era G ℝ:=
  let T:=paceT R.draws.S m t
  current R Q (scaled φ T (pace_pos ..)) (PermuteLens R.draws R.paid Q N t (brought R.draws R.paid Q N t m b))
    t K N (y/T) o

theorem appointment (R:Realm G (e+1) U)(Q:SealR G)(φ:Rarity Q.D)(b:Q.Rider)(t m K N:ℕ)(y:ℝ)(o:CellR):
    asking R Q φ b t m K N y o=away R.draws R.paid Q φ b t m K N y o:=rfl

theorem hearing (R:Realm G (e+1) U)(Q:SealR G)(ear:PassportC H R Q W V)(φ:Rarity Q.D)(b:Q.Rider)
    (t m K N:ℕ)(old:R.anchor ≤ t)(before:t ≤ m)(home:m ≤ K)(top:K ≤ N)(y:ℝ)(o:CellR):
    arm R.draws R.paid Q φ b m K N y o=((paceT R.draws.S m t)^Q.h)⁻¹ • asking R Q φ b t m K N y o:=by
  rw [appointment,←ear.lands,←ear.modes]
  rw [WilsonIndependentMatchedOwnHomeRoster.placed Q ear.f.arch φ b t m K N (ear.tap.symm ▸ old) before home top]
  rw [inv_smul_smul₀ (pow_ne_zero _ (pace_pos ..).ne')]

theorem original (R:Realm G (e+1) U)(Q:Fin (n+1)→SealR G)(ear:HorizonP H R W V Q)
    (φ:Wilt Q)(b:Herit Q)(homes:Fin (n+1)→ℕ)(m K N:ℕ)(awake:∀i,R.anchor ≤ homes i)
    (before:∀i,homes i ≤ m)(home:m ≤ K)(top:K ≤ N)(y:ℝ)(o:CellR):
    let A:=R.draws
    let O:=R.paid
    Ashore Q A O φ (normalized A O Q b m N) m K N y o=
      ∑a:(∀i,Alma (Q i).F),affiled (reel (relativeC A O N m (K-m)) (∏i,b i (a i)))
        ((∏i,((paceT A.S m (homes i))^(Q i).h)⁻¹) • MassP G ℝ n
          (fun i=>asking R (Q i) (φ i) (axis (Q i) (a i)) (homes i) m K N y o)):=by
  intro A O
  have lic (i:Fin (n+1))(a:Alma (Q i).F):Auth (Q i).h (arm A O (Q i) (φ i) (axis (Q i) a) m K N y o):=by
    let P:PassportC H R (Q i) W V:=(ear i).some
    change Auth _ (arm R.draws R.paid _ _ _ _ _ _ _ _)
    rw [←P.lands,←P.modes]
    exact WilsonIndependentSpoutMasterArms.licensed _ P.f.arch _ _ m K N (P.tap.symm ▸ ((awake i).trans ((before i).trans home))) top y o
  rw [WilsonIndependentSpoutMasterArms.original A O Q φ b m K N y o lic]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (affiled _)
  change MassP G ℝ n (fun i=>arm R.draws R.paid (Q i) (φ i) (axis (Q i) (a i)) m K N y o)=_
  have reframe i:=hearing R (Q i) ((ear i).some) (φ i) (axis (Q i) (a i)) (homes i) m K N (awake i) (before i) home top y o
  simp_rw [reframe]
  exact WilsonIndependentMatchedOwnHomeRoster.real_product _ _

end YM.Integration.WilsonIndependentMatchedOwnHomeBasis
end
