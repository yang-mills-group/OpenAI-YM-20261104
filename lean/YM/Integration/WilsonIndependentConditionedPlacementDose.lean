import YM.Integration.WilsonIndependentConditionedPairFour
import YM.Integration.WilsonIndependentConditionedBankMatrix

/-! The full independent reported source determined by the common quiet, dates and K-stencil before taking any realization of the true assigned cut. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPlacementDose
open Finset Function Lattice RG Wilson Source Labels PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open PhysicalNext.Repeat.Legato
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonIndependentConditionedBankMatrix (sample)
open WilsonIndependentConditionedPairFour (Assigned)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open scoped BigOperators Classical

local notation "J" => Fin 2
local notation "C" => Credit.leanC
variable {G:Gauge}{e k u₀ u b host m K N j:ℕ}{R:Run G}

def source (V:Realm G (e+1) C)(Q:SealR G)(k N m K:ℕ)(pt:TowerS G Q.D):Q.Rider:=
  matrix (Wray V.draws V.paid Q.ans Q.path N m)
    (opal Q.F (spools V.draws V.paid N k Q.h m (K-m) pt))

variable {Q:J→SealR G}{own:∀s,Rails (Q s).h k u₀ e}{V:Realm G (e+1) C}{coins:Prices}
variable {port:∀s,Home R (Q s) (own s) j}{ι:J→Type*}{pt:(s:J)→ι s→TowerS G (Q s).D}{fare:(s:J)→ι s→ℝ}
variable (T:Assigned R Q own V coins j port ι pt fare u b host m K N)

theorem original (s:J)(i:ι s):
    publicDose (Q s) (T.cuts s i) 1=source V (Q s) k N m K (pt s i):=by
  rw [WilsonPositionProgramTrialHomeDose.scaled,one_smul]
  have len:=T.birth s i
  change (T.cuts s i).m+(T.cuts s i).i=K at len
  have atHome:=T.home s i
  have count:(T.cuts s i).i=K-m:=by omega
  rw [WilsonPositionProgramTrialAccrued.home,source,T.levels,T.reset,T.vacuum,T.home,count,T.input]

theorem sampled (s:J)(i:ι s)(q:ℕ)(g:ℝ):
    sample V (Q s) N m host q g (publicDose (Q s) (T.cuts s i) 1)=
      sample V (Q s) N m host q g (source V (Q s) k N m K (pt s i)):=by
  rw [original T]

end YM.Integration.WilsonIndependentConditionedPlacementDose
