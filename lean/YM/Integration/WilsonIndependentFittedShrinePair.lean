import YM.Integration.WilsonIndependentFittedNumericalProduct
import YM.Integration.WilsonIndependentMatchedTopReceipt

/-! The actual fitted Shrine, at its own finite top, for each occupied subface of two sources. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedShrinePair
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension Orb.SlotEvaluation FVA2
open Function Matrix Laurent Bloch Metric FreeResolvent Work.F08 Tree
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source.Drops Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedNamedPair (sectionAt placed printed)
open WilsonIndependentMatchedTopFilm (dose word)
open WilsonIndependentFittedNumericalProduct (fitted numerical gross regroup)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Sample 2)(S:Finset (Fin 2))
variable (d:Fin 2→ℕ)(survey:Fin 2→Bool){h:ℕ}(w:∀i,d i<h)
local notation "F" i:max => R.family.labels.level (d i)

def letters (i:S)(a:Alma (F i.val)):Bare.Series (W.tree Y.F.p) G:=
  printed R W Y (survey i.val) (d i.val) (Y.layout i.val) (sheet (F i.val) a)

def payments (v:(i:Fin 2)→Verse (F i))(b:Fin 2→Volume h)(i:S)(a:Alma (F i.val)):PowerSeries ℂ:=
  dose R (w i.val) (v i.val) (b i.val) a

theorem issued (v:(i:Fin 2)→Verse (F i))(b:Fin 2→Volume h):
    Bare.normalized (W.tree Y.F.p) G (∏i∈S,word R W Y (survey i) i (w i) (v i) (b i))=
      fitted W Y (letters R W Y S d survey) (payments R S d w v b):=by
  unfold fitted
  congr 1
  exact (prod_attach S (fun i=>word R W Y (survey i) i (w i) (v i) (b i))).symm

theorem sale (v:(i:Fin 2)→Verse (F i))(b:Fin 2→Volume h)(Q:ℕ){u:ℝ}(small:|u|≤1):
    let P:=letters R W Y S d survey
    let D:=payments R S d w v b
    ‖cash Q u (Bare.normalized (W.tree Y.F.p) G
        (∏i∈S,word R W Y (survey i) i (w i) (v i) (b i)))-
      numerical W Y P D Q Q u‖≤((S.card:ℝ)+1)*|u|^(Q+1)*gross W Y P D Q:=by
  dsimp only
  rw [issued]
  simpa only [Fintype.card_coe] using regroup W Y (letters R W Y S d survey)
    (payments R S d w v b) Q small

variable {e k m:ℕ}{H:Hol G}{E A K U:Credit}(rails:(i:Fin 2)→Rails (d i) k m e)
    (L:(i:Fin 2)→CutsP H (sectionAt R W (survey i) (d i)) (w i) (rails i) E A K U)
    (top:∀i,(L i).N=(L i).ceilC)

include top in
/-- The coordinate series and the real top Wick jet are from the very same fitted verse. -/
theorem original (b:Fin 2→Volume h)(Q:ℕ){u:ℝ}(small:|u|≤1):
    let D:=payments R S d w (fun i=>(L i).tileP) b
    let P:=letters R W Y S d survey
    (∀i:Fin 2,let x:=L i
      let M:=Shrine x.Ntop x.tileP
      X^WilsonPositionProgramMasterBirth.rank R (d:=d i)*flash (jot (b i) (M.1 Y.F.p.side))=
        ∑a,X^(WilsonPositionProgramMasterBirth.rank R (d:=d i)-valence (F i) a)*
          Blue.soil (WilsonIndependentMatchedTopReceipt.realDose R (w:=w i) (b i) x.tileP a)*
          jet (fun y=>placed R W Y (survey i) (d i) (Y.layout i) (sheet (F i) a)
            (translate (-(chartV Y i)) (mantle y)))) ∧
    ‖cash Q u (Bare.normalized (W.tree Y.F.p) G
        (∏i∈S,word R W Y (survey i) i (w i) (L i).tileP (b i)))-
      numerical W Y P D Q Q u‖≤((S.card:ℝ)+1)*|u|^(Q+1)*gross W Y P D Q:=by
  exact ⟨fun i=>WilsonIndependentMatchedTopReceipt.original R W Y (survey i) (L i) (top i) i (b i),
    sale R W Y S d survey w (fun i=>(L i).tileP) b Q small⟩

end YM.Integration.WilsonIndependentFittedShrinePair
