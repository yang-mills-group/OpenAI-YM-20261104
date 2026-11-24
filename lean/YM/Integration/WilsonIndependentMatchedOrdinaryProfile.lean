import YM.Integration.WilsonIndependentMatchedOrdinarySeat
import YM.Integration.WilsonIndependentMatchedCoverProfile

/-! A smooth test at its appointed physical scale is a finite sum of actual
translated, rank-normalized group jets before the matched conditional integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedOrdinaryProfile
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open PertExtension RegulatorIR RegulatorIR.Halo PowerSeries
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open WilsonIndependentMatchedOrdinaryRay (group)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentMatchedCoverProfile (word)
open scoped Classical BigOperators ContDiff
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" =>R.family.labels.level d

def normalized (n:Side)(s:Bool)(a:(F).Index)(o:Cover):Ink (Woods G n):=
  PowerSeries.mk fun j=>coeff (j+((F).grades a).2) (jet (group R W s a o))

theorem named {n:Side}(s:Bool)(a:(F).Index)(o:Cover)(v:TreeVars G n):
    here n v (normalized R W n s a o)=
      shelter ((F).grades a).2 (WilsonIndependentRawNamedStencil.shifted R W s d a o) (sample v):=by
  ext1 j
  have h:=congrArg (coeff (j+((F).grades a).2)) (WilsonIndependentMatchedOrdinaryRay.registered R W s a o v)
  simpa [WilsonIndependentMatchedOrdinarySeat.here,normalized,coeff_X_pow_mul'] using h.symm

def installed (n:Side)(s:Bool)(w:d<D)(c:Verse F)(o:Cover)(b:Volume D):Ink (Woods G n):=
  ∑a,Blue.soil (realDose R (w:=w) b c a)*normalized R W n s (sheet F a) o

theorem tested {n:Side}(s:Bool)(w:d<D)(c:Verse F)(o:Cover)(b:Volume D)(v:TreeVars G n):
    here n v (installed R W n s w c o b)=received R W s w b c o v:=by
  unfold installed received
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_mul,WilsonIndependentMatchedOrdinarySeat.ground,named]
  rfl

theorem equality {n:Side}{a b:Ink (Woods G n)}(h:∀v:TreeVars G n,here n v a=here n v b):a=b:=by
  ext1 j
  apply MvPolynomial.funext
  intro v
  simpa only [WilsonIndependentMatchedOrdinarySeat.here,coeff_map] using congrArg (coeff j) (h v)

theorem posted (n:Side)(s:Bool)(w:d<D)(c:Verse F)(o:Cover)(b:Volume D):
    let T:=Shrine (plate (sectionAt R W s d) w) c
    flash (skewV (wrap n o) (jot b (T.1 n)))=installed R W n s w c o b:=by
  apply equality
  intro v
  rw [tested]
  exact WilsonIndependentMatchedOrdinarySeat.original R W s w b c o v

def stems (n:Side)(s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ):
    Ink (Woods G n):=
  ∑j∈VisitsT φ x y o, drumB l x • installed R W n s w c j (wheelC x y j φ.ψ o)

theorem original (n:Side)(s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(hx:0<x):
    let T:=Shrine (plate (sectionAt R W s d) w) c
    flash ((word T φ x y o l).1 n)=stems R W n s w c φ x y o l:=by
  dsimp only
  let T:=Shrine (plate (sectionAt R W s d) w) c
  have ⟨_,_,paid⟩:=WilsonIndependentMatchedFiledIncome.named R W s d w le_rfl 0 0
  have ok:On d T:=(paid c).1
  let U (z:Cover):Era G ℝ:=locale o (shoe T φ x y z)
  have hu (z:Cover):Auth d (U z):= locale_val _ (seaWet T φ x y ok z) o
  have hsum:(word T φ x y o l).1 n=∑j∈VisitsT φ x y o,drumB l x • (U j).1 n:=by
    rw [word,pupil_eye l T φ x y o hx]
    simp only [Prod.fst_sum,Prod.smul_fst,Finset.sum_apply,Pi.smul_apply,U]
  change flash ((word T φ x y o l).1 n)=_
  have shell (j:Cover):shellK d (drumB l x • (U j).1 n):=((hu j).μ (drumB l x)).span n
  rw [hsum,flash_term _ (fun j _=>shell j),stems]
  apply Finset.sum_congr rfl
  intro j _
  rw [flash_mu _ ((hu j).span n)]
  apply congrArg ((drumB l x) • ·)
  change flash (skewV (wrap n j) (jot (wheelC x y j φ.ψ o) (T.1 n)))=_
  exact posted R W n s w c j _

end YM.Integration.WilsonIndependentMatchedOrdinaryProfile
