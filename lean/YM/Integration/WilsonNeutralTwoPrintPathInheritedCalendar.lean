import YM.Integration.WilsonNeutralTwoPrintPathInheritedBlocks
import YM.Integration.WilsonNeutralTwoPrintPathPageReturn
import YM.Integration.WilsonNeutralTwoPrintPathItinerary
import YM.Integration.WilsonNeutralTwoPrintPathFixed
import YM.Integration.WilsonReceivedCoverFaces

/-! On a fixed fine-site itinerary the incoming whole independent catalogue may be reprinted before each genuine reset. The retained covered output uses the original count of occupied source indices, including all lower subwords. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathInheritedCalendar
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)


open WilsonReceivedDatedVerseReprint (printed Issued)
open WilsonReceivedCanonicalVerseTrial (result)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open WilsonReceivedCompactVerseEntrance (submit CoverBill)
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Mosaic.Near
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}{H:Fin n→ℕ}{I:Type}[DecidableEq I][Fintype I]{D:I→ℕ}
variable (R:Run G)(k:Fin n→ℕ)(κ:(v:Fin n)→Knob (H v))(pt:Fin n→Chamber)

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (J:I→Finset (Fin n))(c:I→Fin n)(live:∀i,c i∈J i)(W:I→ℝ)(pos:∀i,0≤W i)(e:ℕ):
    ∀ᶠj:ℕ in Filter.atTop,∀b,j<b → ∀(S:Finset I)(a r:ℕ),a ≤ e → ∃C σ:ℝ,0 ≤ C ∧ 0<σ ∧
    ∀N,b ≤ N → ∀(q:(i:Fin n)→Choice R k i)(cells:Digits R.family.path.levels (Fin n))
      (sites:I→Fin n → Cover)(read:(i:I)→Pen H (J i) →L[ℝ] Vote (D i)),(∀i,‖read i‖ ≤ W i) →
    ∀(X:Side)(y:I → Cover)(digit:I→Site (loose R.family.path.levels j).L),
    let old:=fixed R k κ pt N b (j+1) cells q
    let temp:=gathered old k e J c sites read
    let grade:=fun i=>mass k (J i)
    let prior:=temp (chartIn (loose R.family.path.levels j) y digit)
    MarkU y S (spent R grade N j e X temp y digit S a r)
      ((logO R.family.path.levels R.metals.O j N prior grade S).2 a r) σ C:=by
  obtain ⟨_,Q,draws,coins,_⟩:=(FundedMarkedCoverRows.realm R simple salary bought 0
    (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_succ _) e 0 0).exists
  obtain ⟨_,_,birth⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e zero_lt_one
  obtain ⟨j₀,buy⟩:=Filter.eventually_atTop.1
    (WilsonReceivedFixedDigitCanonical.original R k κ pt simple quiet salary bought e)
  filter_upwards [Filter.eventually_ge_atTop (max j₀ Q.anchor)] with j birthday
  intro b before S a r grade
  obtain ⟨s,B,hs,hB,hear⟩:=buy (j+1) (by omega) b before
  let A:=1+∑i,W i*B^(J i).card
  have one:1 ≤ A:=by
    dsimp only [A]
    have positive:0 ≤ B:=zero_le_one.trans hB
    linarith [Finset.sum_nonneg (fun i (_:i∈(Finset.univ:Finset I))=>mul_nonneg (pos i) (pow_nonneg positive (J i).card))]
  let k':=fun i=>mass k (J i)
  obtain ⟨C,σ,budget,width,redeem⟩:=WilsonNeutralTwoPrintPathTariff.submitted (D:=D) (k:=k') Q j (by omega) S a r grade hs
  rw [draws,coins] at redeem
  refine ⟨C*A^S.card,σ,mul_nonneg budget (pow_nonneg (zero_le_one.trans one) _),width,?_⟩
  intro N cutoff q cells sites read funded X y digit old temp ranks prior
  have hw:Wellness k old:=WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N cells
    simple R.alloy.B.ratio _ (birth q).1 _ _ (by omega)
  have wages:CoverBill old e s B:=fun p S l hl r=>((hear N cutoff 1 cells q).1 p S l hl r).access
  have held:=WilsonNeutralTwoPrintPathInheritedBlocks.original old hw hs hB wages J c live sites read
  have charged:amount B J read ≤ A:=by
    dsimp only [WilsonNeutralTwoPrintPathInheritedBlocks.amount,A]
    apply add_le_add_right
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (funded i) (pow_nonneg (zero_le_one.trans hB) _)
  have bill:CoverBill temp e s A:=fun p T q hq r=>
    (held.2.2 p T q hq r).more (pow_le_pow_left₀ (zero_le_one.trans held.1) charged _)
  have paid:=redeem N (before.trans_le cutoff) X temp A one held.2.1 bill y digit
  have enrolled:=WilsonReceivedCompactVerseEntrance.original temp held.2.1 hs one bill
  have solve:∀T,WilsonReceivedCoverGrade.Same e
      ((submit temp k' e) (chartIn (loose R.family.path.levels j) y digit) T)
      (prior T):=fun T q hq=>(enrolled.2.2.1 _ T q hq).1
  have low:=congrFun (WilsonNeutralTwoPrintPathItinerary.step k' R.family.path.levels R.metals.O N j solve S a grade) r
  change MarkU y S _ ((logO _ _ j N _ k' S).2 a r) _ _ at paid
  rw [low] at paid
  exact paid

end YM.Integration.WilsonNeutralTwoPrintPathInheritedCalendar
end
