import YM.Integration.WilsonOriginalCensusUnitRoster
import YM.Integration.WilsonReceivedDepositedOrbitalGrade

/-! Restrict the enrolled canonical marked roster on its actual child coordinates at every age. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFixedRestriction
open Function Finset Lattice RG Wilson Source Labels
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonOriginalCensusUnitVerse (observed)
open WilsonOriginalCensusUnitRoster (prior well)
open scoped BigOperators Classical

variable {G:Gauge}{I J:Type}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]
    (R:Run G)(k:I→ℕ){h:I→ℕ}(κ:(j:I)→Knob (h j))(pt:I→Chamber)
    (q:(j:I)→Choice R k j)(e:J↪I)


theorem age (simple:G.Simple)(N:ℕ)(digit:Digits R.family.path.levels I)(A:Case h)(s:Finset J)
    (days i:ℕ)(live:i+days≤N)(o:I → Cover):
    let V:=R.family.path.levels
    let O:=R.metals.O
    observed (itinerary V O k N digit days i (start R k κ pt q) o) A (s.map e)=
      observed (itinerary V O (k ∘ e) N (fun t=>digit t ∘ e) days i (prior R k κ pt q e) (o ∘ e))
        (fun j=>A (e j)) s:=by
  induction days generalizing i o with
  | zero=>exact WilsonOriginalCensusUnitRoster.entered R k κ pt q e o A s
  | succ days ih=>
    let V:=R.family.path.levels
    let O:=R.metals.O
    let high:=itinerary V O k N digit days (i+1) (start R k κ pt q)
    let low:=itinerary V O (k ∘ e) N (fun t=>digit t ∘ e) days (i+1) (prior R k κ pt q e)
    let y:=chartIn (loose V i) o (digit i)
    have hi:=sound V O k N digit simple R.alloy.B.ratio _ (well R k κ pt q) days (i+1) (by omega : i+1+days≤N)
    have lo:=sound V O (k ∘ e) N (fun t=>digit t ∘ e) simple R.alloy.B.ratio (prior R k κ pt q e)
      (well R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) (fun l=>q (e l))) days (i+1) (by omega : i+1+days≤N)
    have named:mass k (s.map e)=mass (k ∘ e) s:=by simp [mass]
    have same:=ih (i+1) (by omega) y
    change observed (logO V O i N (high y) k) A (s.map e)=
      observed (logO V O i N (low (y ∘ e)) (k ∘ e)) (fun j=>A (e j)) s
    exact (WilsonOriginalCensusUnitVerse.step V O (by omega) simple R.alloy.B.ratio _ (hi.level' y) A (s.map e)).trans <|
      (congrArg₂ (fun d v=>verseI V O i N d v) named same).trans <|
      (WilsonOriginalCensusUnitVerse.step V O (by omega) simple R.alloy.B.ratio _ (lo.level' (y ∘ e)) (fun j=>A (e j)) s).symm

theorem original (simple:G.Simple)(N K i:ℕ)(called:i≤K)(live:K≤N)
    (digit:Digits R.family.path.levels I)(o:I → Cover)(A:Case h)(s:Finset J):
    observed (fixed R k κ pt N K i digit q o) A (s.map e)=
      observed (fixed R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) N K i (fun t=>digit t ∘ e)
        (fun j=>q (e j)) (o ∘ e)) (fun j=>A (e j)) s:=
  age R k κ pt q e simple N digit A s (K-i) i (by omega) o

omit [Fintype I] [Fintype J] in
private theorem amount {g:J→ℕ}(Y:family G h)(Z:family G g)(A:Case h)(B:Case g)
    (s:Finset I)(t:Finset J)(n:Side)(ident:observed Y A s=observed Z B t):
    feeble (levelsO Y) A n s=feeble (levelsO Z) B n t:=by
  have b:=congrArg (fun M:Era G ℝ=>flash (M.1 n)) ident
  change flash (pPly A s ((levelsO Y s).1 n))=flash (pPly B t ((levelsO Z t).1 n)) at b
  exact b

theorem connected (simple:G.Simple)(N K i:ℕ)(called:i≤K)(live:K≤N)
    (digit:Digits R.family.path.levels I)(o:I → Cover)(A:Case h)(s:Finset J)(n:Side):
    readO A (fixed R k κ pt N K i digit q o (s.map e)) n=
      readO (fun j=>A (e j)) (fixed R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) N K i (fun t=>digit t ∘ e)
        (fun j=>q (e j)) (o ∘ e) s) n:=by
  let Y:=fixed R k κ pt N K i digit q o
  let Z:=fixed R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) N K i (fun t=>digit t ∘ e) (fun j=>q (e j)) (o ∘ e)
  have hi:=sound R.family.path.levels R.metals.O k N digit simple R.alloy.B.ratio _ (well R k κ pt q) (K-i) i (by omega : i+(K-i)≤N)
  have lo:=sound R.family.path.levels R.metals.O (k ∘ e) N (fun t=>digit t ∘ e) simple R.alloy.B.ratio _
    (well R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) (fun l=>q (e l))) (K-i) i (by omega : i+(K-i)≤N)
  have full:=WilsonReceivedDepositedOrbitalGrade.restrict e (levels_exp Y (hi.level' o) (hi.quiet' o) A n)
  have low:=levels_exp Z (lo.level' (o ∘ e)) (lo.quiet' (o ∘ e)) (fun j=>A (e j)) n
  have cut:(fun t:Finset J=>feeble (levelsO Y) A n (t.map e))=feeble (levelsO Z) (fun j=>A (e j)) n:=by
    funext t
    exact amount Y Z A (fun j=>A (e j)) (t.map e) t n (original R k κ pt q e simple N K i called live digit o A t)
  rw [cut] at full
  exact congrFun (Equation.unique _ _ _ full low) s

end YM.Integration.WilsonOriginalCensusFixedRestriction
