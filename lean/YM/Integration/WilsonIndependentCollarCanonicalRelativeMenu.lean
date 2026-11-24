import YM.Integration.WilsonIndependentCollarCanonicalRelativeRank
import YM.Integration.WilsonOriginalCensusCanonicalAngularMenu

/-! At a fixed physical period all grades and all faces have one opening.
The common root is unrestricted. Auxiliary fits are imposed only after the
actual named sites, the cutoff and the true period have been fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalRelativeMenu
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


open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)
open private priced_rank weight_le_one from YM.Integration.WilsonOriginalCensusCanonicalAngularSum
open WilsonIndependentCollarOrbitalReception (at_front)

def Paid (Q b:ℕ)(t:Case D)(ε:ℝ)(i per:ℕ):Prop:=
  ∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
    (n:Side),(R.family.side i per).val∣n.val → ∀(y:I → Cover)(S:Finset I)(o:I),o∈S →
    breadth S o 0 (relative S o y)≤b → ∀a,a≤Q → ∀(Y:Stationary.Link G n),‖Y‖≤1 → ∀c:ℂ,
    ∀ᶠu in coverFilter R.family.path.levels.S i n,
      ‖repeated R k κ pt N i seed cells n y S o a t Y c u-
        plottedLow R k κ pt N i seed cells n y S a t Y c‖≤‖c‖*ε

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀b(t:Case D)(ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,Paid R k κ pt Q b t ε i per:=by
  obtain ⟨_,_,seeds⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt Q (s:=1) zero_lt_one
  filter_upwards [WilsonIndependentCollarCanonicalRelativeRank.original R k κ pt simple sale paid Q] with i docket
  intro b t ε positive
  have quoted (S:Finset I)(o:I)(a:Fin (Q+1)):
      ∀ᶠ per:ℕ in atTop,o∈S → ∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n:Side),(R.family.side i per).val∣n.val → ∀(y:I → Cover),breadth S o 0 (relative S o y)≤b →
      ∀(Y:Stationary.Link G n),‖Y‖≤1 → ∀c:ℂ,∀ᶠu in coverFilter R.family.path.levels.S i n,
      ‖repeated R k κ pt N i seed cells n y S o a t Y c u-
        plottedLow R k κ pt N i seed cells n y S a t Y c‖≤‖c‖*ε:=by
    by_cases member:o∈S
    · let ord:=mass k S+a.val
      let ranks:=range (ord+1)
      let count:ℝ:=(ord+1:ℕ)
      have one:0<count:=by dsimp [count]; positivity
      let test:=Complex.ofRealCLM.comp (touch t S)
      filter_upwards [ranks.eventually_all.2 fun r _=>docket S o member a r (by omega) b ‖test‖
        (ε/count) (div_pos positive one)] with per priced
      intro _ N newer seed cells n div y close Y unit c
      have legal:Wellness k (fixed R k κ pt N (i+1) i cells seed):=
        WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N cells simple R.alloy.B.ratio
          _ (seeds seed).1 _ _ (by omega)
      let F:=fun r=>Covered R k κ pt N i seed cells S a r
      let g:=fun r (u:Covers R.family.path.levels.S i n)=>copyRead R k κ pt N i seed cells S o a r n
        (R.family.side i u.val) u.prop (y o) (relative S o y) test (weight Y)
      let point:=fun r=>Complex.ofReal (MvPolynomial.eval (coordinates G n Y)
        (paint r (fun z=>touch t S (plume (F r y) n z))))
      have named:(fixed R k κ pt N (i+1) i cells seed) (ink S o (y o) (relative S o y)) S=
          (fixed R k κ pt N (i+1) i cells seed) y S:=legal.filial _ _ S (at_front S o y)
      have rows(r:ℕ)(hr:r∈ranks):∀ᶠu in coverFilter R.family.path.levels.S i n,
          ‖g r u-point r‖≤ε/count:=by
        have fee:=priced r hr N newer seed cells n div (y o) (relative S o y) close test
          (weight (r:=r) Y) 1 zero_le_one (weight_le_one Y unit) (by rw [mul_one])
        have orbit:F r (ink S o (y o) (relative S o y))=F r y:=congrArg (fun M=>M.2 a.val r) named
        change ∀ᶠ u in coverFilter R.family.path.levels.S i n,
          ‖g r u-∑z,test (plume (F r (ink S o (y o) (relative S o y))) n z)*weight Y z‖≤ε/count at fee
        rw [orbit,priced_rank] at fee
        exact fee
      filter_upwards [ranks.eventually_all.2 rows] with u fees
      have diag:plottedLow R k κ pt N i seed cells n y S a t Y c=c*∑r∈ranks,point r:=by
        simp only [plottedLow,diagonal,Complex.ofReal_sum];rfl
      change ‖c*(∑r∈ranks,g r u)-plottedLow R k κ pt N i seed cells n y S a t Y c‖≤_
      rw [diag,←mul_sub,←sum_sub_distrib,norm_mul]
      calc
        _ ≤ ‖c‖*(∑r∈ranks,ε/count):=mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr=>fees r hr)) (norm_nonneg _)
        _ = _:=by
          have sum:∑r∈ranks,ε/count=count*(ε/count):=by simp [ranks,count,nsmul_eq_mul]
          rw [sum,mul_div_cancel₀ _ one.ne']
    · exact Eventually.of_forall fun _ impossible=>False.elim (member impossible)
  filter_upwards [eventually_all.2 fun S=>eventually_all.2 fun o=>eventually_all.2 fun a=>quoted S o a]
    with per filed
  intro N live seed cells n div y S o here close a within Y unit c
  exact filed S o ⟨a,by omega⟩ here N live seed cells n div y close Y unit c

end YM.Integration.WilsonIndependentCollarCanonicalRelativeMenu
end

