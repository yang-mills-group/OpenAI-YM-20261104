import YM.Integration.WilsonMarkedFiniteIndependentHistory
import YM.Integration.WilsonMarkedIndependentNormalizedRecursion
import YM.Integration.WilsonMarkedIndependentPhysicalIntake

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildProgram
open Function Finset Filter Lattice RG Wilson Gauge Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Soil
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonMarkedFiniteIndependentHistory (probe)
open scoped BigOperators Classical Topology
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι→ℕ}

def engineering (P:Patch)(d:ι→ℕ)(S:Finset ι):ℝ:=∏v∈S,(P.L.val:ℝ)^(d v)

def plant (P:Patch)(d:ι→ℕ)(X:Outerm G D):Outerm G D:=fun loc S=>
  engineering P d S • tuftV (mend P (inflate P S 0) D S) (X (splitQ P loc S 0) S)

def next (A:Levels G)(O:ChartRatio G)(N j:ℕ)(d k:ι→ℕ)(X:Outerm G D):Outerm G D:=
  plant (ll A j) d (fun y=>logO A O j N (X y) k)

def history (A:Levels G)(O:ChartRatio G)(N:ℕ)(d k:ι→ℕ)(X:Outerm G D):ℕ→ℕ→Outerm G D
  | 0,_=>X
  | h+1,j=>next A O N j d k (history A O N d k X h (j+1))

theorem healthy (A:Levels G)(O:ChartRatio G){N j:ℕ}(live:j<N)(simple:G.Simple)(ratio:LocalRatio O)
    (d:ι→ℕ)(X:Outerm G D)(income:Wellness k X):Wellness k (next A O N j d k X):=by
  let P:=ll A j
  refine ⟨?_,?_,?_⟩
  · intro x
    change engineering P d ∅ • tuftV (mend P (inflate P ∅ 0) D ∅) (logO A O j N (X (splitQ P x ∅ 0)) k ∅)=0
    rw [logHush,tuftZero,smul_zero]
  · intro x S
    let z:=splitQ P x S 0
    exact ((step_L A O j N (X z) k live simple ratio (income.level' z) S).tuft _).μ _
  · intro x y S same
    let z:=splitQ P x S 0
    let w:=splitQ P y S 0
    have here:∀E⊆S,X z E=X w E:=fun E sub=>income.filial z w E fun b hb=>by
      dsimp only [z,w,splitQ,copyQ]
      rw [same b (sub hb)]
    exact congrArg (fun H=>engineering P d S • tuftV (mend P (inflate P S 0) D S) H) (log_g here)

theorem lawful (A:Levels G)(O:ChartRatio G)(N j h:ℕ)(active:j+h≤N)(simple:G.Simple)(ratio:LocalRatio O)
    (d:ι→ℕ)(X:Outerm G D)(income:Wellness k X):Wellness k (history A O N d k X h j):=by
  induction h generalizing j with
  | zero=>exact income
  | succ h ih=>exact healthy A O (by omega) simple ratio d _ (ih (j+1) (by omega))

/-- The true native normalized one-source return at one fixed child, including
the inherited finite quiet action and the ordinary field-coordinate projector. -/
theorem singleton (A:Levels G)(O:ChartRatio G){N j:ℕ}(live:j<N)(simple:G.Simple)(ratio:LocalRatio O)
    (d:ι→ℕ)(X:Outerm G D)(income:Wellness k X)(y:ι → Cover)(v:ι):
    let P:=ll A j
    let z:=splitQ P y {v} 0
    next A O N j d k X y {v}=(P.L.val:ℝ)^(d v) •
      tuftV (mend P (inflate P {v} 0) D {v}) (verseI A O j N (mass k {v}) (X z {v})):=by
  intro P z
  change engineering P d {v} • tuftV _ (logO A O j N (X z) k {v})=_
  rw [WilsonMarkedIndependentNormalizedRecursion.singleton A O j N live simple ratio (X z)
    (income.level' z) (income.quiet' z) v]
  rw [engineering,Finset.prod_singleton]

/-- The fixed-child summand in the finite formal Gaussian table has exactly
the source engineering factor, before any average over residues. -/
theorem observed (P:Patch)(d:ι→ℕ)(X:Outerm G D)(loc:ι → Cover)(S:Finset ι)(f:Pen D S→L[ℝ]ℝ)
    (n:Side)(e r:ℕ):
    (tuftV f (plant P d X loc S)).1 n e r=
      engineering P d S • (tuftV (probe P S f 0) (X (splitQ P loc S 0) S)).1 n e r:=by
  funext v
  let measure:=WilsonMarkedFiniteIndependentHistory.coeff f n e r v
  change measure (engineering P d S • tuftV (mend P (inflate P S 0) D S) (X (splitQ P loc S 0) S))=_
  rw [map_smul]
  rfl

end YM.Integration.WilsonPointChildProgram
end
