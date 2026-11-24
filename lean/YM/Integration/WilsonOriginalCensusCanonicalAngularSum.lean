import YM.Integration.WilsonOriginalCensusCanonicalCofinal
import YM.Integration.WilsonIndependentCollarCanonicalDeckPortrait
import YM.Integration.WilsonIndependentCollarOrbitalReception

/-! On the first dated Wilson edge, sum the covered relative-copy limit at the
actual tested link, through the finite rank available at this coupling grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalAngularSum
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

def weight {n:Side}(Y:Stationary.Link G n){r:ℕ}(z:Fin r→Site n×Hooks G):ℂ:=
  ∏v:Fin r,((coordinates G n Y (z v)):ℂ)

private theorem weight_le_one {n:Side}(Y:Stationary.Link G n)(unit:‖Y‖≤1){r:ℕ}(z:Fin r→Site n×Hooks G):
    ‖weight Y z‖≤1:=by
  simpa only [weight,WilsonIndependentCollarAngularPeg.multiplier,Complex.ofReal_prod] using
    WilsonIndependentCollarAngularPeg.unit_cap Y unit z

private theorem first_fee {x y z:ℂ}{b:ℝ}(h:‖x-z‖+‖y-z‖≤b):‖x-z‖≤b:=
  (le_add_of_nonneg_right (norm_nonneg (y-z))).trans h

omit [Fintype I] [DecidableEq I] in
private theorem priced_rank (t:Case D)(S:Finset I){n:Side}(Y:Stationary.Link G n)(r:ℕ)
    (T:(Fin r→Site n×Hooks G)→Pen D S):
    ∑z,(Complex.ofRealCLM.comp (touch t S)) (T z)*weight Y z=
      Complex.ofReal (MvPolynomial.eval (coordinates G n Y) (paint r (fun z=>touch t S (T z)))):=by
  simp only [Blue.toll,weight,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_prod]
  rfl

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀(S:Finset I)(o:I),o∈S → ∀a,a≤Q → ∀b(t:Case D)(ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n:Side),(R.family.side i per).val∣n.val → ∀(y:I → Cover),
      breadth S o (y o) (relative S o y)≤b →
      Wellness k (fixed R k κ pt N (i+1) i cells seed) →
      ∀(Y:Stationary.Link G n),‖Y‖≤1 → ∀c:ℂ,
      let ord:=mass k S+a
      let funs:=fun (u:Covers R.family.path.levels.S i n)=>
        c*∑r∈range (ord+1),copyRead R k κ pt N i seed cells S o a r n
          (R.family.side i u.val) u.prop (y o) (relative S o y) (Complex.ofRealCLM.comp (touch t S)) (weight Y)
      let covered:=c*Complex.ofReal (diagonal ord
        (fun r z=>touch t S (plume (Covered R k κ pt N i seed cells S a r y) n z)) (coordinates G n Y))
      ∃z,Tendsto funs (coverFilter R.family.path.levels.S i n) (𝓝 z) ∧
        ‖z-covered‖≤‖c‖*((ord+1:ℕ):ℝ)*ε:=by
  filter_upwards [WilsonOriginalCensusCanonicalCofinal.original R k κ pt simple sale paid Q] with i offer
  intro S o occupied a grade b t ε pos
  let test:=Complex.ofRealCLM.comp (touch t S)
  let ranks:=range (mass k S+a+1)
  filter_upwards [(eventually_all_finset ranks).2 (fun r _=>offer S o occupied a r grade b ‖test‖ ε pos)]
    with per bought
  intro N afterK seed cells n div y near legal Y unit c ord funs covered
  let filter:=coverFilter R.family.path.levels.S i n
  letI:NeBot filter:=coverFilter_neBot R.kit.floor i n
  let F:=fun r=>Covered R k κ pt N i seed cells S a r
  let g:=fun (r:ℕ)(u:Covers R.family.path.levels.S i n)=>copyRead R k κ pt N i seed cells S o a r n
    (R.family.side i u.val) u.prop (y o) (relative S o y) test (weight Y)
  let point:=fun r=>Complex.ofReal (MvPolynomial.eval (coordinates G n Y)
    (paint r (fun z=>touch t S (plume (F r y) n z))))
  let actual:=fun r=>limUnder filter (g r)
  have filed:(fixed R k κ pt N (i+1) i cells seed) (ink S o (y o) (relative S o y)) S=
      (fixed R k κ pt N (i+1) i cells seed) y S:=legal.filial _ _ S (at_front S o y)
  have reads(r:ℕ)(hr:r∈ranks):Tendsto (g r) filter (𝓝 (actual r)) ∧ ‖actual r-point r‖≤ε:=by
    obtain ⟨hi,fee⟩:=bought r hr N afterK seed cells n div (y o) (relative S o y) near test
      (weight (r:=r) Y) 1 zero_le_one (weight_le_one Y unit) (by rw [mul_one])
    change Tendsto (g r) filter (𝓝 _) at hi
    have conv:Tendsto (g r) filter (𝓝 (actual r)):=by
      unfold actual
      rw [hi.limUnder_eq]
      exact hi
    have paidErr:‖actual r-∑z,test (plume (F r (ink S o (y o) (relative S o y))) n z)*weight Y z‖≤ε:=
      first_fee fee
    have orbit:F r (ink S o (y o) (relative S o y))=F r y:=congrArg (fun M=>M.2 a r) filed
    rw [orbit,priced_rank] at paidErr
    exact ⟨conv,paidErr⟩
  refine ⟨c*∑r∈ranks,actual r,?_,?_⟩
  · exact tendsto_const_nhds.mul (tendsto_finsetSum ranks fun r hr=>(reads r hr).1)
  · have diag:covered=c*∑r∈ranks,point r:=by simp only [covered,diagonal,Complex.ofReal_sum];rfl
    rw [diag,←mul_sub,←sum_sub_distrib,norm_mul]
    calc
      _ ≤ ‖c‖*(∑r∈ranks,ε):=mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr=>(reads r hr).2)) (norm_nonneg _)
      _ = _:=by simp [ranks,ord,nsmul_eq_mul,mul_assoc]

end YM.Integration.WilsonOriginalCensusCanonicalAngularSum
end
