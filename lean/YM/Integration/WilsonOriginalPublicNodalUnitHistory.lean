import YM.Integration.WilsonOriginalPublicNodalUnitSeeds
import YM.Integration.WilsonReceivedFixedDigitFinite
import YM.Integration.WilsonOriginalCensusUnitRoster

/-! The same submitted unit erases at every finite ultraviolet cap along
the original fixed child history. Its siblings keep their full marked
program and the actual accumulated vacuum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalUnitHistory
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Bank
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open FormalBulk08.Series
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedCanonicalSocketSeed (contact present)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitHistory (Digits itinerary sound)
open WilsonReceivedFixedDigitFinite (computed)
open WilsonOriginalCensusUnitVerse (observed)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(u:G.ColorIndex)
local notation "L" => R.family.path.levels
variable (tags:∀ i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (d:I→ℕ){D:I→ℕ}(pt:I→Chamber)(q:(i:I)→Choice R d i)
local notation "seed" => start R d (fun i=>contact (D i)) pt q
local notation "A" => present D

include u tags in
theorem grades (simple:G.Simple)(price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)
    (N m a b:ℕ)(live:m<N)(X:Era G ℝ)(left:Auth a X)(right:Auth b X):
    verseI L R.metals.O m N a X=verseI L R.metals.O m N b X:=by
  apply Auth.ext (Auth.verse L live simple R.alloy.B.ratio left) (Auth.verse L live simple R.alloy.B.ratio right)
  funext n
  have ha:=WilsonMarkedFiniteIndependentStep.original R u tags simple price funded N m a live X left n
  have hb:=WilsonMarkedFiniteIndependentStep.original R u tags simple price funded N m b live X right n
  exact ha.trans hb.symm

include u tags in
theorem original (simple:G.Simple)(price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)
    (N:ℕ)(cells:Digits L I)(days m:ℕ)(upper:m+days≤N)(x:I → Cover)
    (s:Finset I)(j:I)(inside:j∈s)(unit:q j=.inl ()):
    let M:=itinerary L R.metals.O d N cells days m seed x
    observed M A s=observed M A (s.erase j):=by
  have well:=WilsonOriginalCensusUnitRoster.well R d (fun i=>contact (D i)) pt q
  induction days generalizing m x with
  | zero=>exact WilsonOriginalPublicNodalUnitSeeds.birth R d (D:=D) pt q x s j inside unit
  | succ days ih=>
    let older:=itinerary L R.metals.O d N cells days (m+1) seed
    let y:=chartIn (loose L m) x (cells m)
    have live:m<N:=by omega
    have prior:m+1+days≤N:=by omega
    have paid:=sound L R.metals.O d N cells simple R.alloy.B.ratio seed well days (m+1) prior
    have previous:=ih (m+1) prior y
    change observed (logO L R.metals.O m N (older y) d) A s=
      observed (logO L R.metals.O m N (older y) d) A (s.erase j)
    rw [WilsonOriginalCensusUnitVerse.step L R.metals.O live simple R.alloy.B.ratio _ (paid.level' y) A s,
      WilsonOriginalCensusUnitVerse.step L R.metals.O live simple R.alloy.B.ratio _ (paid.level' y) A (s.erase j)]
    change observed (older y) A s=observed (older y) A (s.erase j) at previous
    have first:Auth (mass d s) (observed (older y) A (s.erase j)):=previous ▸ ((placedO _ (paid.level' y) s).tuft _)
    rw [previous]
    exact grades R u tags simple price funded N m _ _ live _ first ((placedO _ (paid.level' y) (s.erase j)).tuft _)

end YM.Integration.WilsonOriginalPublicNodalUnitHistory
end
