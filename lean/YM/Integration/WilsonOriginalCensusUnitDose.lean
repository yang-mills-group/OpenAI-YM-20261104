import YM.Integration.WilsonOriginalCensusFixedUnit

/-! Spend the actual signed finite basis dose on the very same original fixed trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusUnitDose
open Function Finset Lattice RG Wilson Source Labels
open Precision Laurent Marker WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open PhysicalNext.Repeat.Legato
open WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords
open WilsonReceivedFixedDigitCanonical WilsonReceivedFixedDigitHistory
open WilsonIndependentCollarOrbitalBasisPayment
open WilsonIndependentCollarOriginalDose WilsonIndependentCollarPaidWindingPanel
open WilsonOriginalCensusUnitLamp (fee)
open scoped BigOperators Classical

variable {G:Gauge}{n:ℕ}(R:Run G)(k:Fin n→ℕ){h:Fin n→ℕ}
  (κ:(j:Fin n)→Knob (h j))(pt:Fin n→Chamber)
  (N per K m i:ℕ)(x:(j:Fin n)→R.family.label (k j))
  (digit:Digits R.family.path.levels (Fin n))(o:Fin n → Cover)
  (A:Case h)(board:Side)

def enrolled (s:Finset (Fin n))(a:Choices R k s)(j:Fin n):Choice R k j:=
  if hv:j∈s then a ⟨j,hv⟩ else .inl ()

def measured (s:Finset (Fin n))(a:Choices R k s):Ink (Woods G board):=
  readO A ((fixed R k κ pt N K i digit (enrolled R k s a) o) s) board

theorem original (simple:G.Simple)(called:i≤K)(live:K≤N)
    (s:Finset (Fin n))(v:Fin n)(hv:v∈s)(zero:k v=0)(mixed:s≠{v})
    (read:Ink (Woods G board)→ℂ)(dark:read 0=0):
    ∑a:Choices R k s,signed R k N per K m x s a*read (measured R k κ pt N K i digit o A board s a)=0:=by
  apply sum_eq_zero
  intro a _
  let j:s:=⟨v,hv⟩
  cases arm:a j with
  | inl u=>
    cases u
    have unit:enrolled R k s a v=.inl ():=by simpa [enrolled,hv,j] using arm
    have clear:=WilsonOriginalCensusFixedUnit.connected R k κ pt _ simple v zero unit N K i called live digit o A s hv board
    change readO A _ board=_ at clear
    simp only [if_neg mixed] at clear
    rw [measured,clear,dark,mul_zero]
  | inr t=>
    have off:¬WilsonOriginalCensusSocketUnit.retained R k s a:=by
      intro yes
      have keep:=yes j (by change k v<4;omega)
      rw [arm] at keep
      contradiction
    rw [WilsonOriginalCensusSocketUnit.supported R simple k N per K x m s a off,zero_mul]

theorem singleton (simple:G.Simple)(called:i≤K)(live:K≤N)(v:Fin n)(zero:k v=0)
    (read:Ink (Woods G board)→ℂ):
    ∑a:Choices R k {v},signed R k N per K m x {v} a*
      read (measured R k κ pt N K i digit o A board {v} a)=
      x v 0*read (fee κ pt A v • 1):=by
  let one:Choices R k {v}:=fun _=>.inl ()
  rw [Finset.sum_eq_single one]
  · have unit:enrolled R k {v} one v=.inl ():=by simp [enrolled,one]
    have seen:=WilsonOriginalCensusFixedUnit.connected R k κ pt _ simple v zero unit N K i called live digit o A
      {v} (mem_singleton_self v) board
    have price:signed R k N per K m x {v} one=x v 0:=by
      simp [signed,one,dose,WilsonThermometerDeclaredSeeds.entry,pole,WilsonOriginalStarSceneWords.scalar,zero]
    have seen':measured R k κ pt N K i digit o A board {v} one=fee κ pt A v • 1:=by
      simpa [measured] using seen
    rw [price,seen']
  · intro a _ different
    have off:¬WilsonOriginalCensusSocketUnit.retained R k {v} a:=by
      intro yes
      apply different
      funext j
      have jv:j.val=v:=mem_singleton.mp j.property
      exact yes j (by rw [jv,zero];omega)
    rw [WilsonOriginalCensusSocketUnit.supported R simple k N per K x m {v} a off,zero_mul]
  · simp

end YM.Integration.WilsonOriginalCensusUnitDose
