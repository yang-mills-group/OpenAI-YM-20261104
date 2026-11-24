import YM.Integration.WilsonNeutralTwoPrintPathBoxLimit
import YM.Integration.WilsonNeutralTwoPrintPathInheritedCalendar
import YM.Integration.WilsonNeutralTwoPrintPathInheritedMotion
import YM.Integration.WilsonNeutralReceivedCoverLimit

/-! The earned, independently reprinted occupied temporary sources have a
cofinal received value on the actual original cover filter. The same complex
number is obtained by exhausting their physically admissible relative shifts
in the previously declared fixed-K cohort. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxReturn
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


open FVA1Physical TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open WilsonNeutralTwoPrintPathBoxSweep (retained)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonOriginalCensusDeckMean (mean)
open WilsonReceivedFixedDigitIntake (next)
open scoped Topology

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (J:I→Finset (Fin n))(c:I→Fin n)(live:∀i,c i∈J i)(W:I→ℝ)(pos:∀i,0≤W i)(e:ℕ):
    ∀ᶠj:ℕ in Filter.atTop,∀b,j<b → ∀(S:Finset I)(o:I),o∈S → ∀(a r:ℕ),a ≤ e →
    ∀N,b ≤ N → ∀(q:(i:Fin n)→Choice R k i)(cells:Digits R.family.path.levels (Fin n))
      (sites:I→Fin n → Cover)(read:(i:I)→Pen H (J i) →L[ℝ] Vote (D i)),(∀i,‖read i‖ ≤ W i) →
    ∀(grid:Side)(digit:I→Site (loose R.family.path.levels j).L)
      (origin:Cover)(base:(S.erase o) → Cover)
      (root:(u:Covers R.family.path.levels.S j grid)→Site (R.family.side j u.val))
      (pins:(u:Covers R.family.path.levels.S j grid)→(S.erase o)→Site (R.family.side j u.val)),
      (∀u,splitter u.prop (root u)=wrap grid origin) →
      (∀u i,splitter u.prop (pins u i)=wrap grid (origin+base i)) →
    ∀(test:Pen D S →L[ℝ] ℂ)(weights:(Fin r→Site grid×Hooks G)→ℂ),
    let old:=fixed R k κ pt N b (j+1) cells q
    let temp:=gathered old k e J c sites read
    let rank:=fun i=>mass k (J i)
    let F:=fun y=>(next R.family.path.levels R.metals.O j N rank temp digit y S).2 a r
    let X:=fun u:Covers R.family.path.levels.S j grid=>R.family.side j u.val
    let prior:=fun (u:Covers R.family.path.levels.S j grid) y=>spent R rank N j e (X u) temp y digit S a r
    let high:=fun u=>mean u.prop (plotted u.prop S o (root u) (pins u) (prior u) test weights)
    let low:=fun M=>retained grid S o origin base M F test weights
    Tendsto high (coverFilter R.family.path.levels.S j grid) (𝓝 (limUnder atTop low)) ∧
    Tendsto low atTop (𝓝 (limUnder (coverFilter R.family.path.levels.S j grid) high)):=by
  obtain ⟨_,_,birth⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e zero_lt_one
  obtain ⟨j₀,buy⟩:=Filter.eventually_atTop.1
    (WilsonReceivedFixedDigitCanonical.original R k κ pt simple quiet salary bought e)
  filter_upwards [Filter.eventually_ge_atTop j₀,
    WilsonNeutralTwoPrintPathInheritedCalendar.original R k κ pt simple quiet salary bought J c live W pos e]
    with j onset delivered
  intro b before S o anchor a r grade N cutoff q cells sites read funded grid digit origin base root pins center addresses
    test weights old temp rank F X prior high low
  letI:NeBot (coverFilter R.family.path.levels.S j grid):=coverFilter_neBot R.kit.floor j grid
  obtain ⟨s,B,hs,hB,hear⟩:=buy (j+1) (by omega) b before
  have hw:Wellness k old:=WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N cells
    simple R.alloy.B.ratio _ (birth q).1 _ _ (by omega)
  have wages:CoverBill old e s B:=fun p T l hl z=>((hear N cutoff 1 cells q).1 p T l hl z).access
  have healthy:=WilsonNeutralTwoPrintPathInheritedBlocks.original old hw hs hB wages J c live sites read
  obtain ⟨C,σ,_,hs,give⟩:=delivered b before S a r grade
  let height:=∑x:Fin r→Site grid×Hooks G,‖weights x‖
  have bounded (x):‖weights x‖ ≤ height:=Finset.single_le_sum (fun i _=>norm_nonneg (weights i)) (Finset.mem_univ x)
  have same (v:Cover)(y:I → Cover)(ghost:wrap grid v=0):plume (F (fun i=>v+y i)) grid=plume (F y) grid:=
    WilsonNeutralTwoPrintPathInheritedMotion.period R.family.path.levels R.metals.O j N (by omega) simple R.alloy.B.ratio
      (fun i=>WilsonNeutralTwoPrintPathInherited.atom old k e (sites i) (J i) (c i) (read i))
      healthy.2.1 digit S y (fun i=>v+y i) v (fun _ _=>rfl) grid ghost a r
  obtain ⟨z,realized,declared⟩:=WilsonNeutralTwoPrintPathBoxLimit.original X
    (cover_size R.family.path.levels.S j grid) (fun u=>u.prop) S o anchor origin base root pins center addresses prior F σ C hs
    (fun u y=>give N cutoff q cells sites read funded (X u) y digit) same test weights height
    (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) bounded
  change Tendsto high _ (𝓝 z) at realized
  change Tendsto low _ (𝓝 z) at declared
  rw [declared.limUnder_eq,realized.limUnder_eq]
  exact ⟨realized,declared⟩

end YM.Integration.WilsonNeutralTwoPrintPathBoxReturn
end
