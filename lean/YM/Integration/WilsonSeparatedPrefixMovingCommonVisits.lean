import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonSeparatedPrefixMovingJointAddress
import YM.Integration.WilsonSeparatedPrefixMovingCenterPrint
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Every captured basis field paired with a fixed exterior has an exact
older cell-integral reading. The connected near term and all older proper
faces use the original submitted `LodeStar` at each genuine visit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCommonVisits
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical



open WilsonSeparatedPrefixMovingJointCell (toll)

open WilsonSeparatedPrefixMovingCellFactor (constant)
open WilsonIndependentMatchedCoverProfile
variable {G:Gauge}{H:Hol G}{n e h k D b m N older:ℕ}{C W V:Credit}

theorem sample (φ:Rarity D)(ε y:ℝ)(o z:CellR)(s:Cover):
    claim D ⟨⟨0,Nat.zero_lt_succ _⟩,Fin.elim0⟩ z (wheelC ε y s φ.ψ o)=φ.ψ.val (Mer.address ε y o s z.val):=by
  change claim D ⟨⟨0,Nat.zero_lt_succ _⟩,Fin.elim0⟩ z (page _ (sonal ε y o s φ.ψ))=_
  rw [nib _ (Nat.zero_le _) Fin.elim0]
  simp [crease,iteratedFDeriv_zero_apply,sonal]
theorem silent (φ:Rarity D)(ε y:ℝ)(pos:0<ε)(o z:CellR)(s:Cover)(out:s∉VisitsT φ ε y o):
    φ.ψ.val (Mer.address ε y o s z.val)=0:=by
  have no:wheelC ε y s φ.ψ o=0:=by
    by_contra h;exact out ((visiting pos).mpr h)
  rw [←sample φ ε y o z s,no,map_zero]
theorem original (R:Realm G (e+1) C)(Q:Fin (n+1)→SealR G)(roster:HorizonP H R W V Q)
    (φ:Wilt Q)(X:Herit Q)(A:Era G ℝ)(paid:Auth h A)(gate:R.anchor≤b)(ear:older≤b)
    (top:b≤N)(F:Rarity D)(x y:ℝ)(hx:0<x)(o:CellR)(degree q r:ℕ)(w:Fin r→YForest G)
    (seats:Finset Cover)(enrolled:VisitsT F x y o⊆seats):
    (cruises R.draws R.paid N (h+capP Q) b older
      (agateV A (word (AutumnDay R.draws R.paid φ X m b N D) F x y o degree))).2 q r w=
    ∑s∈seats,drumB degree x*
      ∫z:CellR,(cruises R.draws R.paid N (h+capP Q) b older (agateV A
        (locale z (shifted (LodeStar R.draws R.paid φ X m b N (paceT R.draws.S m b)) s)))).2 q r w*
        F.ψ.val (Mer.address x y o s z.val) ∂dayMeasure:=by
  rw [WilsonSeparatedPrefixMovingFixedCapture.original R Q roster φ X A paid gate ear top F x y hx o degree q r w]
  apply Finset.sum_subset enrolled
  intro s _ outside
  simp_rw [silent F x y hx o _ s outside,mul_zero,integral_zero,mul_zero]
end YM.Integration.WilsonSeparatedPrefixMovingCommonVisits
