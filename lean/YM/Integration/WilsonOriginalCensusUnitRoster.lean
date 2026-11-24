import YM.Integration.WilsonOriginalCensusUnitVerse
import YM.Integration.WilsonOriginalCensusUnitLamp

/-! The previously nominated canonical sources and their own tests under restriction of names. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusUnitRoster
open Function Finset Lattice RG Wilson Laurent Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open PhysicalNext.Repeat.Legato OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis
open WilsonThermometerDeclaredSeeds WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonOriginalCensusUnitVerse (observed)
open scoped BigOperators Classical

variable {G:Gauge}{I J:Type}[Fintype I][Fintype J][DecidableEq I][DecidableEq J]
    (R:Run G)(k:I→ℕ){h:I→ℕ}(κ:(j:I)→Knob (h j))(pt:I→Chamber)
    (q:(j:I)→Choice R k j)

def view {d:ℕ}(z:Seed G d)(a:Volume d)(o:Cover)(n:Side):Ink (Woods G n):=
  let C:=OriginalMarkedSourceComet.current (colour z.path z.color z.weight z.quadrant) (claim d z.knob z.point)
  flash (Mer.skewV (wrap n o) (jot a ((volumeR C z.head).1 n)))

theorem singleton (o:I → Cover)(A:Case h)(v:I)(n:Side):
    readO A (start R k κ pt q o {v}) n=view (WilsonReceivedCanonicalVerseBasis.basis R k κ pt v (q v)) (A v) (o v) n:=by
  rw [readO,start,IndependentSourcePathFamily.singleton,single,Fintype.sum_unique]
  apply congrArg flash
  funext i r x
  exact petal_hit ..

variable (e:J↪I)

def prior:Outerm G (h ∘ e):=start R (k ∘ e) (fun j=>κ (e j)) (pt ∘ e) (fun j=>q (e j))

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem ink (j:J)(c:Choice R k (e j)):
    WilsonReceivedCanonicalVerseBasis.basis R k κ pt (e j) c=WilsonReceivedCanonicalVerseBasis.basis R (k ∘ e) (fun l=>κ (e l)) (pt ∘ e) j c:=by
  cases c with
  | inl a=>rfl
  | inr a=>rfl

theorem well:Wellness k (start R k κ pt q):=
  (OriginalCoverReanchoring.deposited (offer R k κ pt q) (fun j _=>grade R k κ pt j (q j))).1

theorem entered (o:I → Cover)(A:Case h)(s:Finset J):
    observed (start R k κ pt q o) A (s.map e)=observed (prior R k κ pt q e (o ∘ e)) (fun j=>A (e j)) s:=by
  let Z:=start R k κ pt q o
  let Z':=prior R k κ pt q e (o ∘ e)
  have held:Eu k Z:=(well R k κ pt q).level' o
  have smaller:Eu (k ∘ e) Z':=(well R (k ∘ e) (fun j=>κ (e j)) (pt ∘ e) (fun j=>q (e j))).level' (o ∘ e)
  apply WilsonOriginalCensusUnitVerse.reflected _ _ ((placedO Z held (s.map e)).tuft _) ((placedO Z' smaller s).tuft _)
  intro n
  change readO A (levelsO Z (s.map e)) n=readO (fun j=>A (e j)) (levelsO Z' s) n
  dsimp only [Z,Z',prior]
  have lower:=WilsonReceivedCanonicalSocketLevels.canonical R (k ∘ e) (h:=h ∘ e) (fun j=>κ (e j)) (pt ∘ e) (fun j=>q (e j)) (o ∘ e) (fun j=>A (e j)) n s
  calc
    _=∏j∈s.map e,readO A (Z {j}) n:=WilsonReceivedCanonicalSocketLevels.canonical R k κ pt q o A n (s.map e)
    _=∏j∈s,readO (fun j=>A (e j)) (Z' {j}) n:=?_
    _=_:=lower.symm
  rw [prod_map]
  dsimp only [Z,Z',prior]
  refine prod_congr rfl (fun j _=>?_)
  exact (singleton R k κ pt q o A (e j) n).trans <|
    (congrArg (fun z=>view z (A (e j)) (o (e j)) n) (ink R k κ pt e j (q (e j)))).trans <|
    (singleton R (k ∘ e) (h:=h ∘ e) (fun l=>κ (e l)) (pt ∘ e) (fun l=>q (e l))
      (o ∘ e) (fun l=>A (e l)) j n).symm

end YM.Integration.WilsonOriginalCensusUnitRoster
