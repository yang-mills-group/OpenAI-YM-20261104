import YM.Integration.WilsonOriginalCensusCanonicalOpening

/-! At the genuine first edge the common-copy mean converges to the sum over
relative lifts. Its difference from the specified central cover reading is
uniform in the original UV cutoff on each sufficiently large physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalCofinal
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

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀(J:Finset I)(o:I),o∈J → ∀a r,a≤Q → ∀d (cap ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n:Side),(R.family.side i per).val∣n.val → ∀(origin:Cover)(base:(J.erase o) → Cover),
      breadth J o origin base≤d → ∀(test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)
        (H:ℝ),0≤H → (∀x,‖weights x‖≤H) → ‖test‖*H≤cap →
      let F:=Covered R k κ pt N i seed cells J a r
      let high:=fun u:Covers R.family.path.levels.S i n=>copyRead R k κ pt N i seed cells J o a r n
        (R.family.side i u.val) u.prop origin base test weights
      let low:=fun M=>WilsonNeutralTwoPrintPathBoxSweep.retained n J o origin base M F test weights
      let fixed:=∑z:Fin r→Site n × Hooks G,test (plume (F (ink J o origin base)) n z)*weights z
      Tendsto high (coverFilter R.family.path.levels.S i n) (𝓝 (limUnder atTop low)) ∧
      ‖limUnder (coverFilter R.family.path.levels.S i n) high-fixed‖+
        ‖central R k κ pt N i seed cells J o a r n origin base test weights-fixed‖≤ε:=by
  filter_upwards [WilsonOriginalCensusCanonicalPeriod.issued R k κ pt simple sale paid Q,
    WilsonOriginalCensusCanonicalOpening.original R k κ pt simple sale paid Q] with i income opening
  intro J o member a r grade d cap ε pos
  obtain ⟨C,σ,_,hs,hire⟩:=income J a r grade
  filter_upwards [opening J o member a r grade d cap ε pos] with per bought
  intro N great seed cells n house origin base close test weights H hp bounded budget F high low fixed
  let X:=fun u:Covers R.family.path.levels.S i n=>R.family.side i u.val
  let l:=coverFilter R.family.path.levels.S i n
  letI:NeBot l:=coverFilter_neBot R.kit.floor i n
  have grows:Tendsto (fun u=>(X u).val) l atTop:=cover_size R.family.path.levels.S i n
  let fixedBook:=WilsonReceivedFixedDigitCanonical.fixed R k κ pt N (i+1) i cells seed
  have moves(v:Cover)(y:I → Cover)(hidden:wrap n v=0):
      plume (F (fun s=>v+y s)) n=plume (F y) n:=by
    have cov:=WilsonNeutralTwoPrintPathOldMotion.original R k κ pt simple N (i+1) i (by omega) (by omega) cells seed v
    have exactSites:fixedBook (fun s=>v+y s) J=WilsonCoeffUV.Mer.shifted (fixedBook y J) v:=congrFun (cov y) J
    change plume ((fixedBook (fun s=>v+y s) J).2 a r) n=plume ((fixedBook y J).2 a r) n
    rw [exactSites]
    change plume (revolve v _) n=_
    rw [translated,hidden]
    funext z
    have same:jog (-(0:Site n)) ∘ z=z:=by
      funext m
      ext <;> simp [jog]
    exact congrArg (plume ((fixedBook y J).2 a r) n) same
  obtain ⟨z,upper,lower⟩:=WilsonNeutralTwoPrintPathBoxLimit.original X grows (fun u=>u.prop) J o member origin base
    (fun u=>wrap (X u) origin) (fun u=>homes (X u) origin base)
    (fun u=>Macrame.branch u.prop _) (fun u _=>Macrame.branch u.prop _)
    (fun u=>Actual R k κ pt N i seed cells J a r (X u)) F σ C hs (fun u y=>hire N great seed cells (X u) y)
    moves test weights H hp bounded
  change Tendsto high l (𝓝 z) at upper
  change Tendsto low atTop (𝓝 z) at lower
  have estimate:∀ᶠu in l, ‖high u-fixed‖+‖central R k κ pt N i seed cells J o a r n origin base test weights-fixed‖≤ε:=
    Eventually.of_forall fun u=>bought N great seed cells n (X u) house u.prop origin base close test weights H hp bounded budget
  have final:=le_of_tendsto (((upper.sub (tendsto_const_nhds (x:=fixed))).norm).add tendsto_const_nhds) estimate
  rw [lower.limUnder_eq,upper.limUnder_eq]
  exact ⟨upper,final⟩

end YM.Integration.WilsonOriginalCensusCanonicalCofinal
end
