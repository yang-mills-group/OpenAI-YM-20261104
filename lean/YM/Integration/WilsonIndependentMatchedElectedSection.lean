import YM.Integration.WilsonIndependentMatchedOrdinaryFitted

/-! Use the registered stencil of the actual master when it differs
from either the original field or the canonical survey. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedElectedSection
open Filter Function Matrix Lattice RG Laurent Bloch Metric FreeResolvent Work.F08
open Wilson Tree Precision AnalyticNext.QuarticMatch.Sheets Exterior Next.Free
open Gauge Source Labels XSpace PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.StableStrip
open PowerSeries RegulatorIR
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{D h:ℕ}{F:Labels.Frame G h}(T:SectionData F)(w:h<D)

/-- The specified coefficient of the actual gauge group polynomial, on the
whole ordinary torus before any held-field or vacuum integration. -/
def stencil (n:Side)(a:Alma F)(b:Volume D):Ink (Woods G n):=
  PowerSeries.mk fun j=> coeff (j+valence F a)
    (jewelBloom w a b • jet (fun y:TreeVars G n=>(T.places (Pi.single (sheet F a) 1) 0 (mantle y)).re))

theorem cleared (H:Hol G)(funded:T.Sound H)(starts:Bid.pop T)(n:Side)(a:Alma F)(b:Volume D):
    flash (jot b (herald T w a n))=stencil T w n a b:=by
  ext1 j
  have eq:=congrArg (coeff (j+valence F a)) (herald_lit T w a n b starts H funded)
  simpa [stencil,coeff_X_pow_mul',Plies] using eq

def placed (n:Side)(c:Verse F)(o:Cover)(b:Volume D):Ink (Woods G n):=
  loom (spear (jog (wrap n o):Woods G n≃Woods G n))
    (∑ a,Blue.soil (c a)*stencil T w n a b)

theorem registered (H:Hol G)(funded:T.Sound H)(starts:Bid.pop T)(n:Side)(c:Verse F)(o:Cover)(b:Volume D):
    flash (skewV (wrap n o) (jot b ((Shrine (plate T w) c).1 n)))=placed T w n c o b:=by
  have ⟨_,_,paid⟩:=WilsonIndependentMatchedFiledIncome.original T w H funded starts le_rfl 0 0
  have ok:On h (Shrine (plate T w) c):=(paid c).1
  have array:(Shrine (plate T w) c).1 n=∑a,affix (c a) (herald T w a n):=by
    simp only [Shrine,Stem,vein,Prod.fst_sum,Finset.sum_apply,plate]
  let height:=Finset.univ.sup (valence F)
  have shells a:shellK height (herald T w a n):=by
    have low:valence F a≤height:=Finset.le_sup (Finset.mem_univ a)
    intro i r tall
    exact herald_norm T w a n i r (by omega)
  rw [translate_value n (wrap n o) _ (jot_length b (ok.launch n)),placed,array,map_sum,flash_term _]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [jotAffix,sponsor _ _ (jot_length _ (shells a)),cleared T w H funded starts]
  · intro a _
    exact jot_length _ (affix_shell _ _ (shells a))

def profile (n:Side)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ):Ink (Woods G n):=
  ∑j∈VisitsT φ x y o, drumB l x • placed T w n c j (wheelC x y j φ.ψ o)

theorem original (H:Hol G)(funded:T.Sound H)(starts:Bid.pop T)(n:Side)(c:Verse F)
    (φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(hx:0<x):
    flash ((word (Shrine (plate T w) c) φ x y o l).1 n)=profile T w n c φ x y o l:=by
  let K:=Shrine (plate T w) c
  have ⟨_,_,paid⟩:=WilsonIndependentMatchedFiledIncome.original T w H funded starts le_rfl 0 0
  have ok:On h K:=(paid c).1
  let Z (z:Cover):Era G ℝ:=locale o (shoe K φ x y z)
  have hz (z:Cover):Auth h (Z z):=locale_val _ (seaWet K φ x y ok z) o
  have sum:(word K φ x y o l).1 n=∑j∈VisitsT φ x y o,drumB l x • (Z j).1 n:=by
    rw [word,pupil_eye l K φ x y o hx]
    simp only [Prod.fst_sum,Prod.smul_fst,Finset.sum_apply,Pi.smul_apply,Z]
  change flash ((word K φ x y o l).1 n)=_
  have shell (j:Cover):shellK h (drumB l x • (Z j).1 n):=((hz j).μ (drumB l x)).span n
  rw [sum,flash_term _ (fun j _=>shell j),profile]
  apply Finset.sum_congr rfl
  intro j _
  rw [flash_mu _ ((hz j).span n)]
  exact congrArg ((drumB l x) • ·) (registered T w H funded starts n c j _)

end YM.Integration.WilsonIndependentMatchedElectedSection
