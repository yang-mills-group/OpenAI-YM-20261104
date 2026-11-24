import YM.Integration.WilsonSeparatedPrefixMovingCellFactor
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

theorem scaled (t:ℝ)(A B:Era G ℝ):
    agateV A (t • B)=t • agateV A B:=by
  let o:CellR:=Classical.choice inferInstance
  have scale (Z:Era G Lounge):tuftV (t • century o) Z=t • locale o Z:=rfl
  have factor:=WilsonSeparatedPrefixMovingCellFactor.full (t • century o) A (tuftV constant B)
  rw [scale,scale,WilsonSeparatedPrefixMovingCellFactor.locus] at factor
  have pure:=WilsonSeparatedPrefixMovingCellFactor.full (century o) A (tuftV constant B)
  change locale o _=agateV A (locale o _) at pure
  rw [WilsonSeparatedPrefixMovingCellFactor.locus] at pure
  rw [pure] at factor
  exact factor.symm

private def withField (A:Era G ℝ):Era G ℝ →+ Era G ℝ where
  toFun := agateV A
  map_add' := fun B C=>(WilsonIndependentMatchedTotalTop.binary B C A).2
  map_zero' := by
    have z:=(WilsonIndependentMatchedTotalTop.binary (0:Era G ℝ) 0 A).2
    rw [zero_add] at z
    exact add_left_cancel (z.symm.trans (add_zero _).symm)

theorem settled (R:Realm G (e+1) C){P:Era G ℝ}(paid:Auth k P)(t:ℝ)
    (ear:older ≤ b)(top:b ≤ N):
    cruises R.draws R.paid N k b older (t • P)=t • cruises R.draws R.paid N k b older P:=by
  exact (cruiseT (t • ContinuousLinearMap.id ℝ ℝ) R.draws ear R.hG R.green top paid).symm

private theorem sumPaid (R:Realm G (e+1) C)(ear:older ≤ b)(top:b ≤ N)
    {ι:Type*}(f:Finset ι)(P:ι→Era G ℝ)(hp:∀i∈f,Auth k (P i)):
    cruises R.draws R.paid N k b older (∑i∈f,P i)=∑i∈f,cruises R.draws R.paid N k b older (P i):=by
  classical
  induction f using Finset.induction_on with
  | empty=>
    simp only [Finset.sum_empty]
    have hz:Auth k (0:Era G ℝ):=by let Z:Unit→Era G ℝ:=fun _=>0;simpa using Auth.sum (P:=Z) (S:=∅) (by simp)
    simpa only [sub_self] using (cruisePlus R.draws ear R.hG R.green top hz hz)
  | @insert a f ha ih=>
    have next (i:ι)(hi:i∈f):Auth k (P i):=hp i (Finset.mem_insert_of_mem hi)
    have pa:=hp a (Finset.mem_insert_self _ _)
    have pb:=Auth.sum next
    have sub:=cruisePlus R.draws ear R.hG R.green top (pa.add pb) pb
    rw [add_sub_cancel_right] at sub
    rw [Finset.sum_insert ha,Finset.sum_insert ha,sub_eq_iff_eq_add.mp sub.symm,ih next]

theorem original (R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(roster:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q)(A:Era G ℝ)(paid:Auth h A)(gate:R.anchor ≤ b)(ear:older ≤ b)
    (top:b ≤ N)(F:Rarity D)(x y:ℝ)(hx:0<x)(o:CellR)(degree q r:ℕ)(w:Fin r→YForest G):
    (cruises R.draws R.paid N (h+capP Q) b older
      (agateV A (word (AutumnDay R.draws R.paid φ X m b N D) F x y o degree))).2 q r w=
    ∑site∈VisitsT F x y o,drumB degree x*
      ∫z:CellR,(cruises R.draws R.paid N (h+capP Q) b older (agateV A
        (locale z (shifted (LodeStar R.draws R.paid φ X m b N (paceT R.draws.S m b)) site)))).2 q r w*
        F.ψ.val (Mer.address x y o site z.val) ∂dayMeasure:=by
  classical
  let P:=LodeStar R.draws R.paid φ X m b N (paceT R.draws.S m b)
  have income:Auth (capP Q) P:=cruising R.draws R.hG R.green top le_rfl
    (Hearth_enter roster φ X (gate.trans top) (le_refl N) (m:=m) (y:=paceT R.draws.S m b))
  let lamps:=fun site=>locale o (shoe (AutumnDay R.draws R.paid φ X m b N D) F x y site)
  have intake (s:Cover):lamps s=tuftV (toll F.ψ x y s o) (shifted P s):=rfl
  have lit (s:Cover):Auth (h+capP Q) (agateV A (lamps s)):=by
    rw [intake];exact paid.woadB ((income.shifted s).tuft _) (fun _:Unit=>AlgHom.id ℝ ℝ) (fun _ _ hh=>hh ())
  rw [word,pupil_eye _ _ _ _ _ _ hx]
  change (cruises _ _ _ _ _ _ (withField A (∑s∈VisitsT F x y o,drumB degree x • lamps s))).2 q r w=_
  rw [map_sum]
  change (cruises _ _ _ _ _ _ (∑s∈VisitsT F x y o,agateV A (drumB degree x • lamps s))).2 q r w=_
  simp_rw [scaled]
  rw [sumPaid R ear top _ _ (fun s _=>(lit s).μ _)]
  simp_rw [settled R (lit _) _ ear top]
  simp only [Prod.snd_sum,Finset.sum_apply,Prod.smul_snd,Pi.smul_apply,smul_eq_mul]
  refine Finset.sum_congr rfl fun s _=>?_
  apply congr_arg (fun z:ℝ=>drumB degree x*z)
  rw [intake]
  exact WilsonSeparatedPrefixMovingCellFactor.original R A (shifted P s) paid (income.shifted s) ear top F.ψ x y s o w

end YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
