import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerSite
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRefined
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerKinetic
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerReached
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears coefficients representative)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel row pivot vote)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

open Extra.FD
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPhysicalStationMixedWickSolvent (Room)
open WilsonMeasuredPublicEntranceNativeLowerSignal (difference)
open WilsonMeasuredPublicEntranceNativeLowerTolerance (Meter)
open WilsonMeasuredPublicEntranceNativeLowerTicket (Ticket)
theorem original {U:ℝ→tower S}{r t:ℕ→ℝ}{s:ℝ}{d:ℕ}(u v:(R.family.labels.level d).Index)
    (room:Room R (S:=S) B e a)(le:e≤d)(low:e<d){pick:ℕ→ℕ}(cofinal:Tendsto pick atTop atTop)
    (ratio:Tendsto t atTop (𝓝 s)){g:ℕ→ℝ}(income:∀ᶠi in atTop,1/8≤g i ∧ g i≤12)
    {x:ℕ→Points 2}(hx:Tendsto x atTop (𝓝 room.ξ))
    (issuer:let T:=R.family.labels.level d
      let q:=(T.grades u).2
      let Q:=(T.grades v).2
      ∀j:T.Index,(T.grades j).2=Q→∀tol:ℝ,0<tol→∀ᶠi in atTop,
        let r₀:=r (pick i)
        let t₀:=t (pick i)
        let z:=r₀ • x i
        Meter R F B e a le (U r₀) z q Q (ear R z (U r₀ d ((Bel R.family.book).project d (Pi.single j 1))))
          (difference R U r₀ t₀ (t₀^d*(g i)^q) ((Bel R.family.book).project d (Pi.single u 1))) tol):
    WilsonMeasuredPublicEntranceNativeLowerRefined.Refined R F atTop U r t s d u v:=by
  let q:=((R.family.labels.level d).grades u).2
  obtain ⟨lc,live,sub,b,bpos,_,prices⟩:=WilsonMeasuredPublicEntranceNativeLowerKinetic.original (ratio.comp cofinal) income
  have hb:0≤b:=by linarith only [bpos]
  refine ⟨pick,lc,live,cofinal.mono_left sub,b^q,pow_nonneg hb _,?_⟩
  apply WilsonMeasuredPublicEntranceNativeLowerSite.original R F B e a _ room le low (prices d q) (hx.mono_left sub)
  exact fun j hj tol paid=>(issuer j hj tol paid).filter_mono sub

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerReached
end
