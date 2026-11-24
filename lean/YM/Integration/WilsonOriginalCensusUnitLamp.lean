import YM.Integration.WilsonReceivedCanonicalSocketLevels
import YM.Integration.WilsonOriginalCensusSocketUnit

/-! The undosed canonical unit is the constant angular series on each auxiliary board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusUnitLamp
open Function Finset Lattice RG Wilson Laurent Source Labels Marker Stationary PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Fountain
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open PhysicalNext.Repeat.Legato OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open scoped BigOperators Classical ContDiff

variable {G:Gauge}{I:Type}[DecidableEq I]{h:I→ℕ}

def fee (κ:(j:I)→Knob (h j))(pt:I→Chamber)(A:Case h)(v:I):ℝ:=
  claim (h v) (κ v) (pt v) (A v)

theorem flat {n:Side}(u:ℝ)(o:Site n):
    Mer.skewV o (sprig (fun _:Lawn (Woods G n)=>u) 0)=u • uband 1:=by
  funext j r x
  cases j with
  | zero=>
    cases r with
    | zero=>simp [Mer.skewV,revolve,sprig,Blue.shine,rye,uband]
    | succ r=>simp [Mer.skewV,revolve,sprig,Blue.shine,uband]
  | succ j=>
    simp [Mer.skewV,revolve,sprig,Blue.shine,rye,iteratedFDeriv_const_of_ne,uband]

theorem atSource (v:I)(q:Knob (h v))(t:Chamber)(o:Cover)(A:Case h)(n:Side)
    (path:Fin 0→RG.Slot)(col:Fin 0→G.ColorIndex)
    (coef:∀ j,NativeCurvatureTensor.coefficient col j=1):
    pPly A {v} ((source h v (colour path col 1 Complex.reCLM) q t 0 o).1 n)=
      (claim (h v) q t (A v)) • uband 1:=by
  let P:=colour path col 1 Complex.reCLM
  let W:=current P (claim (h v) q t)
  let L:Vote (h v) →L[ℝ] ℝ:=ContinuousLinearMap.apply ℝ ℝ (A v)
  have located:pPly A {v} ((source h v P q t 0 o).1 n)=
      Mer.skewV (wrap n o) (ply L.toLinearMap ((volumeR W 0).1 n)):=by
    funext j r x
    exact petal_hit ..
  have constant:meter (dip W L) (0:Site n)=fun _=>claim (h v) q t (A v):=by
    funext U
    simp [meter,RG.Atom.unmasked,RG.Atom.poly,Rolls.dip,W,OriginalMarkedSourceComet.current,P,colour,L,coef]
  rw [located,volume_probe,constant]
  simpa only [Nat.zero_le,if_true,Nat.sub_zero] using
    flat (G:=G) (claim (h v) q t (A v)) (wrap n o)

variable [Fintype I](R:Run G)(k:I→ℕ)(κ:(j:I)→Knob (h j))(pt:I→Chamber)

theorem canonical (q:(j:I)→Choice R k j)(v:I)(unit:q v=.inl ())
    (o:I → Cover)(A:Case h)(n:Side):
    pPly A {v} ((start R k κ pt q o {v}).1 n)=fee κ pt A v • uband 1:=by
  unfold start
  rw [IndependentSourcePathFamily.singleton]
  unfold single
  rw [Fintype.sum_unique]
  let filed (b:Choice R k v):Pal ℝ (Woods G n):=
    let z:=WilsonReceivedCanonicalVerseBasis.basis R k κ pt v b
    pPly A {v} ((source h v (colour z.path z.color z.weight z.quadrant) z.knob z.point z.head (o v)).1 n)
  change filed (q v)=_
  rw [unit]
  change pPly A {v} ((source h v (colour (Fin.elim0:Fin 0→RG.Slot)
    (Fin.elim0:Fin 0→G.ColorIndex) 1 Complex.reCLM) (κ v) (pt v) 0 (o v)).1 n)=_
  exact atSource (G:=G) (h:=h) v (κ v) (pt v) (o v) A n Fin.elim0 Fin.elim0
    (fun j=>(color R k (.inl v) j).symm)

theorem reading (q:(j:I)→Choice R k j)(v:I)(unit:q v=.inl ())
    (o:I → Cover)(A:Case h)(n:Side):
    readO A (start R k κ pt q o {v}) n=fee κ pt A v • (1:Ink (Woods G n)):=by
  have bounded:shellK 0 (uband (U:=Woods G n) 1):=by
    rw [←pen_puff h G A n]
    exact ply_shell _ ((paidO (j:=0) h).span n)
  rw [readO,canonical R k κ pt q v unit o A n,flash_mu _ bounded,uband_flash,map_one]

end YM.Integration.WilsonOriginalCensusUnitLamp
