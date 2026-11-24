import YM.Integration.WilsonIndependentFittedPublicLetters
import YM.Integration.WilsonIndependentFittedNumericalTail
import YM.Integration.WilsonIndependentFittedShrineSalary
import YM.Integration.WilsonPositionThermometerGradedSource

/-! All proper faces on the actual sample, evaluated with one common fitted verse at
every occurrence of a source. The unfunded raw-to-public change of basis is visible
in the individual normalized bare pivot differences. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedShrineFaces
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension Orb.SlotEvaluation FVA2
open Function Matrix Laurent Bloch Metric FreeResolvent Work.F08 Tree
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source.Drops Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedNamedPair (sectionAt placed printed)
open WilsonIndependentMatchedTopFilm (dose word)
open WilsonIndependentFittedNumericalProduct (fitted numerical gross pivot regroup)
open WilsonIndependentFittedPublicLetters (placement)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){n:ℕ}(Y:Sample n)(S:Finset (Fin n))
variable (d:Fin n→ℕ)(survey:Fin n→Bool){h:ℕ}(w:∀i,d i<h)
local notation "F" i:max => R.family.labels.level (d i)
variable {e k m:ℕ}{H:Hol G}{E A K U:Credit}(rails:(i:Fin n)→Rails (d i) k m e)
    (L:(i:Fin n)→CutsP H (sectionAt R W (survey i) (d i)) (w i) (rails i) E A K U)
    (top:∀i,(L i).N=(L i).ceilC)

def arm(i:Fin n)(a:Alma (F i)):Bare.Series (W.tree Y.F.p) G:=
  printed R W (placement Y i) (survey i) (d i) (Y.layout i) (sheet (F i) a)

def bills(b:Fin n→Volume h)(i:Fin n)(a:Alma (F i)):PowerSeries ℂ:=dose R (w i) (L i).tileP (b i) a

def face(b:Fin n→Volume h):PowerSeries ℂ:=
  Bare.normalized (W.tree Y.F.p) G
    (∏i∈S,word R W (placement Y i) (survey i) 0 (w i) (L i).tileP (b i))

local notation "P" => (fun i:S=>arm R W Y d survey (Subtype.val i))
local notation "D" b:max => (fun i:S=>bills R W d survey w rails L b (Subtype.val i))

theorem filed (b:Fin n→Volume h):face R W Y S d survey w rails L b=fitted W Y P (D b):=by
  let row (i:Fin n):Bare.Series (W.tree Y.F.p) G:=
    word R W (placement Y i) (survey i) 0 (w i) (L i).tileP (b i)
  change Bare.normalized (W.tree Y.F.p) G (∏i∈S,row i)=Bare.normalized (W.tree Y.F.p) G (∏i:S,row i.val)
  exact congrArg (Bare.normalized (W.tree Y.F.p) G) (prod_attach S row).symm

def remainder (b:Fin n→Volume h)(Q J:ℕ)(u:ℝ):ℝ:=
  WilsonIndependentFittedNumericalTail.tariff W Y P (D b) Q J u

theorem retained (b:Fin n→Volume h)(Q J:ℕ){u:ℝ}(small:|u|≤1):
    ‖cash Q u (face R W Y S d survey w rails L b)-numerical W Y P (D b) Q J u‖≤
      ((S.card:ℝ)+1)*|u|^(Q+1)*gross W Y P (D b) Q+remainder R W Y S d survey w rails L b Q J u:=by
  rw [filed]
  simpa only [Fintype.card_coe,remainder] using
    WilsonIndependentFittedNumericalTail.original W Y P (D b) Q J small

include top in
/-- Every tap of this sample belongs to the same genuinely chosen fitted top. -/
theorem recorded (b:Fin n→Volume h)(i:Fin n):
    let τ:=L i
    let M:=Shrine τ.Ntop τ.tileP
    X^WilsonPositionProgramMasterBirth.rank R (d:=d i)*flash (jot (b i) (M.1 Y.F.p.side))=
        ∑a,X^(WilsonPositionProgramMasterBirth.rank R (d:=d i)-valence (F i) a)*
          Blue.soil (WilsonIndependentMatchedTopReceipt.realDose R (w:=w i) (b i) τ.tileP a)*
          jet (fun y=>placed R W (placement Y i) (survey i) (d i) (Y.layout i) (sheet (F i) a)
            (translate (-(chartV Y i)) (mantle y))):=
  WilsonIndependentMatchedTopReceipt.original R W (placement Y i) (survey i) (L i) (top i) 0 (b i)

abbrev rose(i:Fin 3):ℕ:=(WilsonPositionThermometerGradedSource.grade i).val

theorem thermometer (Y:Sample 3)(survey:Fin 3→Bool){h:ℕ}(w:∀i,rose i<h)
    {e k m:ℕ}{H:Hol G}{E A K U:Credit}(v:(i:Fin 3)→Rails (rose i) k m e)
    (L:(i:Fin 3)→CutsP H (sectionAt R W (survey i) (rose i)) (w i) (v i) E A K U)
    (b:Fin 3→Volume h)(Q J:ℕ){u:ℝ}(small:|u|≤1):
    ∀S:Finset (Fin 3),let P':=fun i:S=>arm R W Y rose survey i.val
      let D':=fun i:S=>bills R W rose survey w v L b i.val
      ‖cash Q u (face R W Y S rose survey w v L b)-numerical W Y P' D' Q J u‖≤
        ((S.card:ℝ)+1)*|u|^(Q+1)*gross W Y P' D' Q+remainder R W Y S rose survey w v L b Q J u:=
  fun S=>retained R W Y S rose survey w v L b Q J small

end YM.Integration.WilsonIndependentFittedShrineFaces
