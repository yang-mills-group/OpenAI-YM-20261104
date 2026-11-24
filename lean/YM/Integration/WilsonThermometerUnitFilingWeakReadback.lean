import YM.Integration.WilsonMarkedIndependentNormalizedRecursion
import YM.WilsonCoeffUV.Marked.Bounds.Penalty

/-! Withdraw a face of the complete ordinary generator on its own transformed subcells, then pass the assembled scalar through a single genuine normalized Wick operator. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakReadback
open Filter Function Finset Lattice Wilson RG Laurent Precision WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators
variable {G:Gauge} {ι V W:Type} [DecidableEq ι] {D:ι→ℕ}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

def map (T:V→L[ℝ]W):Era G V→ₗ[ℝ]Era G W where
  toFun:=tuftV T
  map_add' X Y:=by
    apply Prod.ext
    · funext n a r z;exact T.map_add _ _
    · funext a r z;exact T.map_add _ _
  map_smul' t X:=by
    apply Prod.ext
    · funext n a r z;exact T.map_smul _ _
    · funext a r z;exact T.map_smul _ _

structure Note (D:ι→ℕ) (W:Type) [NormedAddCommGroup W] [NormedSpace ℝ W] where
  face : Finset ι
  site : ι→ Cover
  test : Pen D face→L[ℝ]W
  factor : ℝ

def hear (p:Note D W)(X:Outerm G D):Era G W:=
  p.factor • map p.test (levelsO (X p.site) p.face)

def child (P:Patch)(K:ι→ℕ)(p:Note D W)(j:backRow P.L p.face):Note D W where
  site:=splitQ P p.site p.face j
  face:=p.face
  test:=p.test.comp (mend P (inflate P p.face j) D p.face)
  factor:=p.factor*scalesK P K p.face

variable [CompleteSpace W]

theorem original (A:Levels G)(L:ChartRatio G)(K k:ι→ℕ)(N b i:ℕ)(bn:b ≤ N)(ib:i<b)
    (X:Outerm G D)(stock:Wellness k X)(simple:G.Simple)(localRatio:LocalRatio L)
    (p:Note D W)(height:ℕ)(cap:mass k p.face ≤ height):
    hear p (Gears A L K k N b i X) =
      verseI A L i N height (∑j:backRow (ll A i).L p.face,
        hear (child (ll A i) K p j) (Gears A L K k N b (i+1) X)):=by
  let P:=ll A i
  let Z:=Gears A L K k N b (i+1) X
  have co:=Cog (K':=K) A L bn X stock simple localRatio (Nat.succ_le_of_lt ib)
  let word (j:backRow P.L p.face):=levelsO (Z (splitQ P p.site p.face j)) p.face
  let test (j:backRow P.L p.face):=p.test.comp (mend P (inflate P p.face j) D p.face)
  have auth (j:backRow P.L p.face):Auth (mass k p.face) (word j):=
    placedO _ (co.level' _) _
  have valid (j:backRow P.L p.face):Auth height (tuftV (test j) (word j)):=
    ((auth j).tuft _).tall cap
  have edge:=congrFun (MeterC (K':=K) A L bn X stock simple localRatio ib p.site) p.face
  change p.factor • map p.test _ = verseI A L i N height
    (∑j:backRow P.L p.face,(p.factor*scalesK P K p.face) • tuftV (test j) (word j))
  rw [edge]
  change p.factor • map p.test
    (∑j:backRow P.L p.face,scalesK P K p.face •
      tuftV (mend P (inflate P p.face j) D p.face) (verseI A L i N (mass k p.face) (word j)))=_
  rw [map_sum,Finset.smul_sum,verse_sum A simple (ib.trans_le bn) localRatio (fun j _=>valid j)]
  apply sum_congr rfl
  intro j _
  rw [map_smul,smul_smul]
  apply congrArg (fun u:Era G W=>(p.factor*scalesK P K p.face) • u)
  change tuftV (test j) (verseI A L i N (mass k p.face) (word j))=_
  rw [ply_verse A (ib.trans_le bn) simple localRatio (auth j)]
  exact verseExpand A (ib.trans_le bn) simple localRatio ((auth j).tuft _) cap

end YM.Integration.WilsonThermometerUnitFilingWeakReadback
