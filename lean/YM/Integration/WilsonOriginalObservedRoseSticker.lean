import YM.Integration.WilsonOlderFreshSoftFigures
import YM.Integration.SignedShiftedMeasuredCurrent

/-! The physical derivative and the original group field in each placed Rose atom. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseSticker
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open PhysicalNext.Repeat.Legato OriginalMarkedSourceComet IndependentSourcePathFamily
open private current_poly current_invariant from YM.Integration.OriginalMarkedSourceComet
open private atom from YM.Integration.IndependentSourcePathFamily
open private starts from YM.Integration.SignedShiftedMeasuredCurrent
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}{r:ℕ}

theorem placed (i:I)(P:RG.Atom G r)(legal:P.Invariant)(κ:Knob (D i))(pt:Chamber)
    (A:Case D)(o:Cover)(n:Side):
    readO A (source D i P κ pt r o) n=
      jet (fun v:Lawn (Woods G n)=>claim (D i) κ pt (A i) * P.unmasked (mantle v) (wrap n o)):=by
  let C:=current P (claim (D i) κ pt)
  let L:Vote (D i) →L[ℝ] ℝ:=ContinuousLinearMap.apply ℝ ℝ (A i)
  let T:=dip C L
  have admitted:Auth 0 (volumeR C r):=aug_auth C (current_invariant P legal _) (by omega)
  have ear:readO A (tuftV (petal D i) (volumeR C r)) n=
      flash (ply L.toLinearMap ((volumeR C r).1 n)):=by
    apply congrArg flash
    funext j s x
    exact petal_hit ..
  have raw:flash (ply L.toLinearMap ((volumeR C r).1 n))=
      (X:Ink (Woods G n))^r*flash (sprig (meter T (0:Site n)) r):=by
    rw [volume_probe]
    apply PowerSeries.ext
    intro j
    rw [coeff_X_pow_mul']
    unfold Blue.flash
    simp only [coeff_mk]
    split_ifs <;> simp [T,totalR]
  change readO A (shifted (tuftV (petal D i) (volumeR C r)) o) n=_
  have stamped:Auth 0 (tuftV (petal D i) (volumeR C r)):=admitted.tuft (petal D i)
  rw [transportPage _ stamped,ear,raw,map_mul,map_pow]
  change (loom (SignedShiftedMeasuredCurrent.shift o) X)^r *
      loom (SignedShiftedMeasuredCurrent.shift o) (flash (sprig (meter T (0:Site n)) r))=_
  rw [show loom (SignedShiftedMeasuredCurrent.shift (G:=G) (f:=n) o) X=X by simp [loom],
    SignedShiftedMeasuredCurrent.sprig_at,starts]
  apply congrArg jet
  funext v
  change (dip (current P _) L).poly _=_
  rw [current_poly]
  rfl

omit [DecidableEq I] in
theorem group (R:Run G)(d:I→ℕ)(b:∀i,(R.family.labels.level (d i)).Index)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(A:Case D)(i:I){n:Side}(z:Site n)(U:Config G n):
    (∑m, claim (D i) (κ i) (pt i) (A i) *
       (atom (WilsonOlderFreshSoftFigures.seed R D d b κ pt i m)).unmasked U z)=
      claim (D i) (κ i) (pt i) (A i) * ((R.family.localSection (d i)).places (Pi.single (b i) 1) z U).re:=by
  rw [WilsonOlderFreshSoftFigures.field R D d b κ pt i,Finset.mul_sum]

end YM.Integration.WilsonOriginalObservedRoseSticker
