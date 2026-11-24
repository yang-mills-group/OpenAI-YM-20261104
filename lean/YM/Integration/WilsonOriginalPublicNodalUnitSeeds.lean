import YM.Integration.WilsonOriginalCensusUnitVerse
import YM.Integration.WilsonOriginalCensusUnitLamp
import YM.Integration.WilsonReceivedCanonicalSocketSeed
import YM.Integration.WilsonReceivedCanonicalSocketLevels
import YM.Integration.WilsonOriginalPublicNodalOrbitWord

/-! A genuinely filed unit evaluates to one on its public point sheet, even
when its assigned engineering grade is positive. The ordinary original
source and the separately nominated orbital source then lose the same slot. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalUnitSeeds
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open WilsonOriginalStarSceneWords (raw)
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonReceivedCanonicalSocketSeed (contact present sheet)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonOriginalCensusUnitVerse (observed)
open scoped Classical BigOperators ContDiff

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
    (pt:I→Chamber)(q:(i:I)→Choice R d i)
local notation "κ" => (fun i=>contact (D i))

omit [Fintype I] [DecidableEq I] in
theorem evaluation (j:I):
    WilsonOriginalCensusUnitLamp.fee κ pt (present D) j=1:=by
  change claim (D j) ⟨⟨0,Nat.zero_lt_succ _⟩,Fin.elim0⟩ (pt j) (page _ (sheet _))=1
  rw [nib _ (Nat.zero_le _) Fin.elim0]
  simp [crease,WilsonReceivedCanonicalSocketSeed.sheet,iteratedFDeriv_zero_apply]

theorem birth (x:I → Cover)(s:Finset I)(j:I)(inside:j∈s)(unit:q j=.inl ()):
    observed (start R d κ pt q x) (present D) s=
      observed (start R d κ pt q x) (present D) (s.erase j):=by
  let Y:=start R d κ pt q x
  have earned:Eu d Y:=IndependentSourcePathFamily.legal _ x
    (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R d κ pt j (q j))
  apply WilsonOriginalCensusUnitVerse.reflected _ _
    ((placedO Y earned s).tuft (touch (present D) s))
    ((placedO Y earned (s.erase j)).tuft (touch (present D) (s.erase j)))
  intro n
  change readO (present D) (levelsO Y s) n=readO (present D) (levelsO Y (s.erase j)) n
  unfold Y
  rw [WilsonReceivedCanonicalSocketLevels.canonical,WilsonReceivedCanonicalSocketLevels.canonical,
    ←Finset.prod_erase_mul s _ inside,WilsonOriginalCensusUnitLamp.reading R d κ pt q j unit,
    evaluation,one_smul,mul_one]

omit [Fintype I] [DecidableEq I] in
theorem group (j:I)(unit:q j=.inl ()){n:Side}(W:Config G n)(o:Site n):
    (raw R d (entry R d j (q j))).unmasked W o=1:=by
  rw [unit]
  simp [WilsonThermometerDeclaredSeeds.entry,WilsonOriginalStarSceneWords.raw,WilsonOriginalStarSceneWords.rank,RG.Atom.unmasked,RG.Atom.poly]

omit [Fintype I] in
theorem grouped (s:Finset I)(j:I)(inside:j∈s)(unit:q j=.inl ())(z:I→ Cover)(P:XSpace.Period):
    WilsonOriginalPublicNodalOrbitWord.body R d s z (fun i=>q i) P=
      WilsonOriginalPublicNodalOrbitWord.body R d (s.erase j) z (fun i=>q i) P:=by
  funext W
  let f:=fun i=>(raw R d (entry R d i (q i))).unmasked W (wrap P.side (z i))
  change (∏v:s,f v)=∏v:s.erase j,f v
  rw [Finset.prod_coe_sort,Finset.prod_coe_sort,←Finset.prod_erase_mul s f inside]
  rw [show f j=1 from group R d q j unit W _,mul_one]

end YM.Integration.WilsonOriginalPublicNodalUnitSeeds
end
