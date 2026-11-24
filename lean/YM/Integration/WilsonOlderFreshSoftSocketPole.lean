import YM.Integration.WilsonOriginalChargedSourceHead
import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! The physical positive-rank socket and its prescribed lowered thermal address have one marked history at planting. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketPole
open Function Finset Lattice Wilson RG Source Labels
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Soil
open OriginalMarkedSourceComet IndependentSourcePathFamily WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (offer start)
open WilsonReceivedCanonicalVerseBasis (basis)
open WilsonOriginalStarSceneWords (pole rank)
open WilsonCoeffUV.Mer.Rolls
open FormalBulk08 WilsonCoeffUV.Winding PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G)(d:I→ℕ){D:I→ℕ}
variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R d i)

def raw (i:I)(_a:Unit):Seed G (D i):=
  {WilsonReceivedCanonicalVerseBasis.basis R d κ pt i (q i) with head:=rank R d (entry R d i (q i))}

def lag (i:I):ℕ:=pole R d (entry R d i (q i))

omit [Fintype I] in
theorem incoming (i:I)(y:Cover)(n:Side)(j:ℕ):
    let high:=single (WilsonOlderFreshSoftSocketPole.raw R d κ pt q) i y
    let low:=single (WilsonReceivedCanonicalVerseRegister.offer R d κ pt q) i y
    let shift:=lag R d q i
    (high.1 n) (j+shift)=(low.1 n) j ∧ high.2 (j+shift)=low.2 j ∧
      (j<shift → (high.1 n) j=0 ∧ high.2 j=0):=by
  let a:=WilsonReceivedCanonicalVerseBasis.basis R d κ pt i (q i)
  let A:=colour a.path a.color a.weight a.quadrant
  have fit:lag R d q i≤a.rank:=WilsonOriginalStarSceneWords.low R d _
  dsimp only
  simp only [single,Fintype.sum_unique]
  exact ⟨WilsonOriginalChargedSourceHead.finite i A (κ i) (pt i) y fit n j,
    WilsonOriginalChargedSourceHead.covered i A (κ i) (pt i) y fit j,
    fun hj=>WilsonOriginalChargedSourceHead.before i A (κ i) (pt i) y fit n j hj⟩

omit [Fintype I] in
theorem radial (i:I)(y:Cover)(n:Side)(test:Case D):
    WilsonCoeffUV.Wheel.Mark.readO test (single (WilsonOlderFreshSoftSocketPole.raw R d κ pt q) i y) n=
      PowerSeries.X^(lag R d q i)*WilsonCoeffUV.Wheel.Mark.readO test (single (WilsonReceivedCanonicalVerseRegister.offer R d κ pt q) i y) n:=by
  let a:=WilsonReceivedCanonicalVerseBasis.basis R d κ pt i (q i)
  let A:=colour a.path a.color a.weight a.quadrant
  have fit:lag R d q i≤a.rank:=WilsonOriginalStarSceneWords.low R d _
  simp only [single,Fintype.sum_unique]
  exact WilsonOriginalChargedSourceHead.radial i A (κ i) (pt i) y fit n test

end YM.Integration.WilsonOlderFreshSoftSocketPole
end
