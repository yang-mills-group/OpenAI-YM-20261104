import YM.Integration.WilsonSeparatedPrefixMovingPinFlow
import YM.Integration.WilsonSeparatedPrefixMovingSummedCenter
import YM.Integration.WilsonSeparatedPrefixMovingJointAddress

/-! The same capture-site pin on the full older field and on its two actual input factors. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinProduct
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonIndependentMovingRosterCut (parcel)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonSeparatedPrefixMovingSummedCenter (issued)
open WilsonSeparatedPrefixMovingPinFlow (packet)
open WilsonPositionProgramPinnedHearthHistory (pin)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{e n:ℕ}{E:Credit}
private theorem product {A U V:Type*}[AddGroup A][NormedRing V][NormedAlgebra ℝ V]
    (P Q:Pal V (A×U))(a:A):skewV a (woad P Q)=woad (skewV a P) (skewV a Q):=by
  funext j r x
  simp only [skewV,woad,revolve,knitS,swirl,webT,Finset.sum_apply,Pi.smul_apply]
  rfl

theorem grouped {V:Type*}[NormedRing V][NormedAlgebra ℝ V](P Q:Era G V)(a:Cover):
    shifted (agateV P Q) a=agateV (shifted P a) (shifted Q a):=
  Prod.ext (funext fun _=>product _ _ _) (product _ _ _)

def landed (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(a:Cover)(y:ℝ)(t m b older N i:ℕ):Era G Lounge:=
  cruises R.draws R.paid N (F.h+capP Q) i older (shifted
    (issued R Q F φ ψ X Y t m i N y) (pin R.draws.S b i a))

theorem original {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(a:Cover)(y:ℝ)(t m b older N i:ℕ)(z:CellR)
    (enrolled:R.anchor ≤ i)(past:older ≤ i)(cut:i ≤ N):
    locale z (landed R Q F φ ψ X Y a y t m b older N i)=
      hear R (F.h+capP Q) N b older a i (packet R Q F φ ψ X Y z y t m N i):=by
  have paid:=WilsonSeparatedPrefixMovingSummedCenter.mounted R Q F φ ψ X Y roster far t m i older N y enrolled past cut
  unfold landed hear locale
  rw [cruiseT (century z) R.draws past R.hG R.green cut (paid.2.2.shifted (WilsonPositionProgramPinnedHearthHistory.pin R.draws.S b i a))]
  apply congr_arg (cruises R.draws R.paid N (F.h+capP Q) i older)
  change shifted (locale z (issued R Q F φ ψ X Y t m i N y)) _=shifted (packet R Q F φ ψ X Y z y t m N i) _
  unfold packet issued
  rw [woadChart,WilsonIndependentMovingRosterCut.located R Q roster φ X z y m i N (enrolled.trans cut) cut]
  rfl

theorem captured {H:Hol G}{W V:Credit}(R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)
    (roster:HorizonP H R W V Q)(far:PassportC H R F W V)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(a:Cover)(t m b older N:ℕ)(z:CellR)
    (enrolled:R.anchor ≤ b)(past:older ≤ b)(cut:b ≤ N):
    locale z (landed R Q F φ ψ X Y a (paceT R.draws.S m b) t m b older N b)=
      cruises R.draws R.paid N (F.h+capP Q) b older (agateV
        (WilsonSeparatedPrefixMovingJointAddress.move a (locale z
          (F.spins R.draws R.paid ψ t b N (paceT R.draws.S t b) Y)))
        (locale z (shifted (LodeStar R.draws R.paid φ X m b N (paceT R.draws.S m b)) a))):=by
  rw [original R Q F roster far φ ψ X Y a _ t m b older N b z enrolled past cut]
  unfold hear packet
  simp only [WilsonPositionProgramPinnedHearthHistory.pin,WilsonPositionProgramPinnedHearthHistory.count,Ico_self,Finset.prod_empty,one_smul]
  change cruises _ _ _ _ _ _ (shifted (agateV _ _) a)=_
  rw [grouped,WilsonIndependentMovingRosterCut.located R Q roster φ X z _ m b N (enrolled.trans cut) cut]
  have hm:paceT R.draws.S m b/paceT R.draws.S m t=paceT R.draws.S t b:=by
    unfold paceT;field_simp [(R.draws.S.a_pos m).ne',(R.draws.S.a_pos t).ne']
  rw [hm]
  rfl
end YM.Integration.WilsonSeparatedPrefixMovingPinProduct
