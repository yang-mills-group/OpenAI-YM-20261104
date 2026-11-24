import YM.Integration.WilsonOriginalCensusCanonicalAngularSum

/-! All original rank-tested masks at the first canonical step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalAngularMenu
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}{e:ℕ}

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonOriginalCensusOrbitCenters (layout shifted)
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)

open WilsonReceivedFixedDigitIntake (next)
open WilsonCoeffUV.Wheel.Motion (steppedC ramble)
open private translated from YM.Integration.WilsonPointChildCenteredSeat

open WilsonNeutralTwoPrintPathStart (returned)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonThermometerDeclaredSeeds
open OriginalMarkedSourceComet
open scoped Topology
variable (R:Run G)(k:I→ℕ)(κ:(v:I)→Knob (D v))(pt:I→Chamber)

open WilsonOriginalCensusCanonicalPeriod (Actual Covered)
open WilsonOriginalCensusCanonicalOpening (copyRead central)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonNeutralTwoPrintPathBoxPlacement (homes)
open scoped Classical BigOperators Topology

open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonIndependentCollarOrbitalReception (relative at_front)
open WilsonOriginalRawQReversion (coordinates)

open WilsonOriginalCensusCanonicalAngularSum (weight)

def repeated (N i:ℕ)(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)(n:Side)
    (y:I → Cover)(S:Finset I)(o:I)(a:ℕ)(t:Case D)(Y:Stationary.Link G n)(c:ℂ)
    (u:Covers R.family.path.levels.S i n):ℂ:=
  c*∑r∈range (mass k S+a+1),copyRead R k κ pt N i seed cells S o a r n (R.family.side i u.val)
    u.prop (y o) (relative S o y) (Complex.ofRealCLM.comp (touch t S)) (weight Y)

def plottedLow (N i:ℕ)(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)(n:Side)
    (y:I → Cover)(S:Finset I)(a:ℕ)(t:Case D)(Y:Stationary.Link G n)(c:ℂ):ℂ:=
  c*Complex.ofReal (diagonal (mass k S+a)
    (fun r z=>touch t S (plume (Covered R k κ pt N i seed cells S a r y) n z)) (coordinates G n Y))

/-- Every nonempty mask shares one physical-period floor, including all choices
of its marked front and all tests at the requested thermal grades. -/
theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀b(t:Case D)(ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n:Side),(R.family.side i per).val∣n.val → ∀(y:I → Cover)(S:Finset I)(o:I),o∈S →
      breadth S o (y o) (relative S o y)≤b → ∀a,a≤Q →
      ∀(Y:Stationary.Link G n),‖Y‖≤1 → ∀c:ℂ,
      let f:=repeated R k κ pt N i seed cells n y S o a t Y c
      let L:=coverFilter R.family.path.levels.S i n
      Tendsto f L (𝓝 (limUnder L f)) ∧
        ‖limUnder L f-plottedLow R k κ pt N i seed cells n y S a t Y c‖≤‖c‖*ε:=by
  obtain ⟨_,_,seeds⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt Q (s:=1) zero_lt_one
  filter_upwards [WilsonOriginalCensusCanonicalAngularSum.original R k κ pt simple sale paid Q] with i docket
  intro b t ε positive
  have quoted (S:Finset I)(o:I)(a:Fin (Q+1)):
      ∀ᶠ per:ℕ in atTop,o∈S → ∀(N:ℕ),i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n:Side),(R.family.side i per).val∣n.val → ∀(y:I → Cover),
      breadth S o (y o) (relative S o y)≤b → ∀(Y:Stationary.Link G n),‖Y‖≤1 → ∀c:ℂ,
      ∃z:ℂ,Tendsto (repeated R k κ pt N i seed cells n y S o a t Y c)
        (coverFilter R.family.path.levels.S i n) (𝓝 z) ∧
        ‖z-plottedLow R k κ pt N i seed cells n y S a t Y c‖≤‖c‖*ε:=by
    by_cases member:o∈S
    · let count:ℝ:=((mass k S+a.val+1:ℕ):ℝ)
      have one:0<count:=by dsimp [count]; positivity
      filter_upwards [docket S o member a (by omega) b t (ε/count) (div_pos positive one)] with per priced
      intro _ N newer seed cells n div y close Y unit c
      have legal:Wellness k (fixed R k κ pt N (i+1) i cells seed):=
        WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N cells simple R.alloy.B.ratio
          _ (seeds seed).1 _ _ (by omega)
      obtain ⟨z,lim,fee⟩:=priced N newer seed cells n div y close legal Y unit c
      refine ⟨z,lim,fee.trans_eq ?_⟩
      change ‖c‖*count*(ε/count)=‖c‖*ε
      field_simp
    · exact Eventually.of_forall fun _ impossible=>False.elim (member impossible)
  filter_upwards [eventually_all.2 fun S=>eventually_all.2 fun o=>eventually_all.2 fun a=>quoted S o a] with per filed
  intro N live seed cells n div y S o here close a within Y unit c f L
  obtain ⟨z,lim,fee⟩:=filed S o ⟨a,by omega⟩ here N live seed cells n div y close Y unit c
  change Tendsto f L (𝓝 z) at lim
  letI:NeBot L:=coverFilter_neBot R.kit.floor i n
  rw [lim.limUnder_eq]
  exact ⟨lim,fee⟩

end YM.Integration.WilsonOriginalCensusCanonicalAngularMenu
end
