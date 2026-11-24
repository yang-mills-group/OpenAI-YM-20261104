import YM.Integration.WilsonOriginalCensusUnitVerse
import YM.Integration.WilsonOriginalCensusUnitLamp
import YM.Integration.WilsonOriginalCensusUnitEquation

/-! Exact unit factorization of the prescribed fixed digit program, all native proper faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFixedUnit
open Function Finset Lattice RG Wilson Source Labels
open PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonOriginalCensusUnitVerse (observed)
open WilsonOriginalCensusUnitLamp (fee)
open scoped BigOperators Classical

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(k:I→ℕ){h:I→ℕ}
  (κ:(j:I)→Knob (h j))(pt:I→Chamber)(q:(j:I)→Choice R k j)

private theorem fresh:Wellness k (start R k κ pt q):=
  (OriginalCoverReanchoring.deposited (offer R k κ pt q)
    (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R k κ pt j (q j))).1

theorem entered (v:I)(unit:q v=.inl ())(A:Case h)(s:Finset I)(hv:v∈s)(o:I → Cover):
    let Y:=start R k κ pt q o
    observed Y A s=fee κ pt A v • observed Y A (s.erase v):=by
  intro Y
  have paid:= (fresh R k κ pt q).level' o
  apply WilsonOriginalCensusUnitVerse.reflected _ _
    ((placedO Y paid s).tuft (touch A s)) (((placedO Y paid (s.erase v)).tuft _).μ _)
  intro n
  change readO A (levelsO Y s) n=flash (fee κ pt A v • pPly A (s.erase v) ((levelsO Y (s.erase v)).1 n))
  rw [flash_mu _ (ply_shell _ ((placedO Y paid (s.erase v)).span n))]
  change readO A (levelsO Y s) n=fee κ pt A v • readO A (levelsO Y (s.erase v)) n
  rw [WilsonReceivedCanonicalSocketLevels.canonical R k κ pt q o A n s,
    WilsonReceivedCanonicalSocketLevels.canonical R k κ pt q o A n (s.erase v),
    ←mul_prod_erase s (fun j=>readO A (start R k κ pt q o {j}) n) hv,
    WilsonOriginalCensusUnitLamp.reading R k κ pt q v unit o A n,smul_mul_assoc,one_mul]

theorem original (simple:G.Simple)(v:I)(zero:k v=0)(unit:q v=.inl ())
    (N K i:ℕ)(called:i≤K)(live:K≤N)(digit:Digits R.family.path.levels I)(o:I → Cover)
    (A:Case h)(s:Finset I)(hv:v∈s):
    let Y:=fixed R k κ pt N K i digit q o
    observed Y A s=fee κ pt A v • observed Y A (s.erase v):=by
  have grade:mass k s=mass k (s.erase v):=by
    have extra:=sum_erase_add (s:=s) k hv
    rw [zero,add_zero] at extra
    exact extra.symm
  exact WilsonOriginalCensusUnitVerse.age R.family.path.levels R.metals.O N digit simple R.alloy.B.ratio
    (start R k κ pt q) (fresh R k κ pt q) A s (s.erase v) grade (fee κ pt A v)
    (entered R k κ pt q v unit A s hv) (K-i) i (by omega) o

theorem connected (simple:G.Simple)(v:I)(zero:k v=0)(unit:q v=.inl ())
    (N K i:ℕ)(called:i≤K)(live:K≤N)(digit:Digits R.family.path.levels I)(o:I → Cover)
    (A:Case h)(s:Finset I)(hv:v∈s)(n:Side):
    let Y:=fixed R k κ pt N K i digit q o
    readO A (Y s) n=if s={v} then fee κ pt A v • 1 else 0:=by
  intro Y
  let M:=feeble (levelsO Y) A n
  let L:=feeble Y A n
  have wellness:=WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N digit
    simple R.alloy.B.ratio (start R k κ pt q) (fresh R k κ pt q) (K-i) i (by omega : i+(K-i)≤N)
  have priced:Eu k Y:=wellness.level' o
  have accepted:=levels_exp Y priced (wellness.quiet' o) A n
  have token:∀t:Finset I,v∈t → M t=(fee κ pt A v • 1)*M (t.erase v):=by
    intro t ht
    have a:=original R k κ pt q simple v zero unit N K i called live digit o A t ht
    have b:=congrArg (fun F:Era G ℝ=>flash (F.1 n)) a
    change M t=flash (fee κ pt A v • pPly A (t.erase v) ((levelsO Y (t.erase v)).1 n)) at b
    rw [flash_mu _ (ply_shell _ ((placedO Y priced (t.erase v)).span n))] at b
    change M t=fee κ pt A v • M (t.erase v) at b
    rw [smul_mul_assoc,one_mul]
    exact b
  have all:=WilsonOriginalCensusUnitEquation.filed M L accepted v (fee κ pt A v • 1) token
  simpa [L,feeble,WilsonOriginalCensusUnitEquation.spike,WilsonOriginalCensusUnitEquation.omitAt,hv] using congrFun all s

end YM.Integration.WilsonOriginalCensusFixedUnit
