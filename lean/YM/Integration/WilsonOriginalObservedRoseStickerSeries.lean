import YM.Integration.WilsonOriginalObservedRoseSticker
import YM.Integration.WilsonIndependentMatchedOpeningRoster
import YM.Integration.WilsonIndependentMatchedOrdinaryProfile

/-! Read the actual tested Rose stencil against the same independently registered public column. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseStickerSeries
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open PertExtension RegulatorIR XSpace XSpace.Rose
open PhysicalNext.Repeat.Legato OriginalMarkedSourceComet IndependentSourcePathFamily
open private atom from YM.Integration.IndependentSourcePathFamily
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOrdinarySeat (here)
open WilsonIndependentMatchedOrdinaryRay (group)
open scoped Classical BigOperators Topology ContDiff

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(D d:I→ℕ)
variable (b:∀i,(R.family.labels.level (d i)).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)

theorem single (o:I→ Cover)(A:Case D)(i:I)(n:Side):
    readO A (WilsonOlderFreshSoftFigures.stencil R D d b κ pt o {i}) n=
      jet (fun v:Lawn (Woods G n)=>claim (D i) (κ i) (pt i) (A i) *
        ((R.family.localSection (d i)).places (Pi.single (b i) 1) (wrap n (o i)) (mantle v)).re):=by
  let term:=WilsonOlderFreshSoftFigures.seed R D d b κ pt i
  let W (m:WilsonMeasuredPointBareWords.Term R (d i) (b i)):Era G (Pen D {i}):=
    source D i (atom (term m)) (κ i) (pt i) (term m).rank (o i)
  let f (m:WilsonMeasuredPointBareWords.Term R (d i) (b i))(v:Lawn (Woods G n)):ℝ:=
    claim (D i) (κ i) (pt i) (A i) * (atom (term m)).unmasked (mantle v) (wrap n (o i))
  have legal m:(atom (term m)).Invariant:=
    OriginalMarkedSourceComet.invariant (term m).path (term m).color (term m).weight (term m).quadrant
  have filed m:Auth 0 (W m):=certified D i _ (legal m) (κ i) (pt i) _ _ (by omega) (o i)
  have smooth m:Green (f m):=contDiffAt_const.mul (meter_hot (atom (term m)) (wrap n (o i))).contDiffAt
  rw [WilsonOlderFreshSoftFigures.stencil,IndependentSourcePathFamily.singleton]
  change flash (pPly A {i} ((∑m,W m).1 n))=_
  have collect:pPly A {i} ((∑m,W m).1 n)=∑m,pPly A {i} ((W m).1 n):=by
    funext j s x
    simp [pPly,ply,Prod.fst_sum,Finset.sum_apply]
  rw [collect,flash_term _ (fun m _=>ply_shell (touch A {i}).toLinearMap ((filed m).span n))]
  calc
    _=∑m,jet (f m):=Finset.sum_congr rfl fun m _=>
      WilsonOriginalObservedRoseSticker.placed i (atom (term m)) (legal m) (κ i) (pt i) A (o i) n
    _=jet (∑m,f m):=(jet_sum Finset.univ f (fun m _=>smooth m)).symm
    _=_:=by
      apply congrArg jet
      funext v
      simpa only [Finset.sum_apply] using
        WilsonOriginalObservedRoseSticker.group R d b κ pt A i (wrap n (o i)) (mantle v)

omit [Fintype I] [DecidableEq I] in
theorem column_raw {a h:ℕ}(W:Initialize G)(cut:a<h)(u:(R.family.labels.level a).Index)(o:Cover)(n:Side):
    (X:Ink (Woods G n))^(((R.family.labels.level a).grades u).2) *
      flash ((column R W false cut (seat (R.family.labels.level a) u) o).1 n)=
      jet (group R W false u o):=by
  apply WilsonIndependentMatchedOrdinaryProfile.equality
  intro v
  rw [map_mul,map_pow,WilsonIndependentMatchedOpeningColumn.ray]
  have hX:here n v X=X:=by simp [WilsonIndependentMatchedOrdinarySeat.here]
  rw [hX]
  exact WilsonIndependentMatchedOrdinaryRay.registered R W false u o v

theorem original (W:Initialize G)(h:I→ℕ)(cut:∀i,d i<h i)(o:I→ Cover)(A:Case D)(i:I)(n:Side):
    readO A (WilsonOlderFreshSoftFigures.stencil R D d b κ pt o {i}) n=
      realS (claim (D i) (κ i) (pt i) (A i)) *
        (X:Ink (Woods G n))^(((R.family.labels.level (d i)).grades (b i)).2) *
         flash ((column R W false (cut i) (seat (R.family.labels.level (d i)) (b i)) (o i)).1 n):=by
  rw [single,mul_assoc,column_raw]
  have product:=jet_mul (f:=fun _:Lawn (Woods G n)=>claim (D i) (κ i) (pt i) (A i))
    (g:=group R W false (b i) (o i)) contDiffAt_const
    (WilsonIndependentMatchedOrdinaryRay.smooth R W false (b i) (o i))
  rw [jet_const] at product
  refine (congrArg jet ?_).trans product
  funext u
  simp only [Pi.mul_apply,WilsonIndependentMatchedOrdinaryRay.group,
    WilsonIndependentMatchedNamedPair.sectionAt,Bool.false_eq_true,if_false]

end YM.Integration.WilsonOriginalObservedRoseStickerSeries
