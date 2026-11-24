import YM.Integration.WilsonAllDateHarvestDescendants
import YM.Integration.WilsonSeparatedOriginalReplicaCubic

/-! Conditional means of a grouped physical clinic on its original positive
Wilson law. The parent, all occupants, and the terminal cutoff are common. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalResidentExpectation
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open RG05Readout.Flatten RG05Readout.Pulse Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open OPE.Therm PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per j k b m:ℕ}

def mean (opened:k+1≤N)(U:Config G (((R.family)).side k per)):ContinuousMap (Config G (R.family.side N per)) ℂ→ₗ[ℂ]ℂ:=
  let law:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per opened U
  haveI : IsProbabilityMeasure law:=WilsonMacroscopicRichFlatPosteriorLaw.prob R opened le_rfl U
  have cost (F:ContinuousMap (Config G (R.family.side N per)) ℂ):Integrable F law:=F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  {toFun:=fun F=>∫V,F V ∂law
   map_add':=fun F H=>integral_add (cost F) (cost H)
   map_smul':=fun a _=>integral_const_mul a _}

theorem value (opened:k+1≤N)(U:Config G (((R.family)).side k per))(F:ContinuousMap (Config G (R.family.side N per)) ℂ):
    mean R opened U F=actualTransport (R.family) (N:=N) F (Nat.le_of_succ_le opened) U:=by
  letI : IsProbabilityMeasure (scene ((R.family)).path N per N):=OPE.Therm.probability R.makes.wilson le_rfl
  have cost:Integrable F (scene ((R.family)).path N per N):=F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact (WilsonMacroscopicRichFlatPosteriorLaw.reading R opened le_rfl U F cost).symm.trans
    (congrFun (WilsonSeparatedOriginalPosteriorTransport.realized R.makes le_rfl (Nat.le_of_succ_le opened) F cost) U)

variable (o:Fin 3→Site (((R.family)).side b per))(E:Fin 3→Motion)(s:Fin 3→ℕ)(q:ManyStem (R.family) o b→Body)
variable (S:(i:Fin 3)→Emblems (R.family) (s i))(x:(i:Fin 3)→Palette (R.family) (s i))

def weight (bj:b≤j)(i:Fin 3)(z:ManyStem (R.family) o j):ℂ:=
  if z.val.1=i then ratioX (((R.family)).S.toDepth bj per) (s z.val.1) else 0

theorem grouped (bj:b≤j)(jN:j≤N)(opened:k+1≤N)(U:Config G (((R.family)).side k per))(i:Fin 3):
    actualTransport (R.family) (N:=N) (clinic (R.family) per N (s i) (Launch (m:=m) s S x i N) b (o i) (E i) (q ((Mine.remap o E).symm i)))
      (Nat.le_of_succ_le opened) U =
    ∑z:ManyStem (R.family) o j, weight R o s bj i z *
      actualTransport (R.family) (N:=N) (WilsonAllDateHarvestPhysical.columns o E s q S x m N j z) (Nat.le_of_succ_le opened) U:=by
  let base:ContinuousMap (Config G (R.family.side N per)) ℂ:=⟨clinic (R.family) per N (s i) (Launch (m:=m) s S x i N) b (o i) (E i) (q ((Mine.remap o E).symm i)),clinic_cut ..⟩
  let f (z:ManyStem (R.family) o j):ContinuousMap (Config G (R.family.side N per)) ℂ:=⟨WilsonAllDateHarvestPhysical.columns o E s q S x m N j z,clinic_cut ..⟩
  have history:base=∑z:ManyStem (R.family) o j,weight R o s bj i z • f z:=by
    apply ContinuousMap.ext;intro V
    have hs:=congrFun (congrFun (WilsonAllDateHarvestDescendants.original o E s q S x (m:=m) bj jN) i) V
    change (∑z:ManyStem (R.family) o j,weight R o s bj i z • WilsonAllDateHarvestPhysical.columns o E s q S x m N j z) V=base V at hs
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply]
    change base V=∑z:ManyStem R.family o j,weight R o s bj i z • WilsonAllDateHarvestPhysical.columns o E s q S x m N j z V
    simpa only [Finset.sum_apply,Pi.smul_apply] using hs.symm
  change actualTransport (R.family) (N:=N) base (Nat.le_of_succ_le opened) U=∑z,weight R o s bj i z * actualTransport (R.family) (N:=N) (f z) (Nat.le_of_succ_le opened) U
  simp_rw [←value R opened U]
  rw [history,map_sum];simp only [map_smul,smul_eq_mul]

end YM.Integration.WilsonSeparatedOriginalResidentExpectation
