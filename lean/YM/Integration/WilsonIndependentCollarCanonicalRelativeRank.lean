import YM.Integration.WilsonOriginalCensusCanonicalCofinal

/-! A common translation can cost auxiliary cover size while leaving the
original physical-period opening dependent only on relative displacements. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalRelativeRank
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


open WilsonOriginalCensusCanonicalOpening (copyRead)
open WilsonNeutralTwoPrintPathBoxPlacement (homes)
open WilsonOriginalCensusCanonicalPeriod (Covered)

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀(J:Finset I)(o:I),o∈J → ∀a r,a≤Q → ∀d (cap ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n:Side),(R.family.side i per).val∣n.val → ∀(origin:Cover)(base:(J.erase o) → Cover),
      breadth J o 0 base≤d → ∀(test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)
        (H:ℝ),0≤H → (∀x,‖weights x‖≤H) → ‖test‖*H≤cap →
      let F:=Covered R k κ pt N i seed cells J a r
      let fixed:=∑z:Fin r→Site n × Hooks G,test (plume (F (ink J o origin base)) n z)*weights z
      ∀ᶠu:Covers R.family.path.levels.S i n in coverFilter R.family.path.levels.S i n,
        ‖copyRead R k κ pt N i seed cells J o a r n (R.family.side i u.val) u.prop
          origin base test weights-fixed‖≤ε:=by
  filter_upwards [WilsonOriginalCensusCanonicalPeriod.issued R k κ pt simple sale paid Q] with i bought
  intro J o active a r grade d cap ε pos
  obtain ⟨C,σ,_,hs,hire⟩:=bought J a r grade
  let A:=C*price J o (Hooks G) r σ 1
  let B:=C*tariff (Hooks G) r σ 1
  filter_upwards [WilsonOriginalCensusOrbitPeriod.cost R i d σ σ (|A| * cap) (|B| * cap) 0 ε hs hs pos]
    with per ready
  intro N great seed cells n pay origin base near test weights H hp bounded budget F fixed
  let side:=fun u:Covers R.family.path.levels.S i n=>R.family.side i u.val
  have grow:Tendsto (fun u=>(side u).val) (coverFilter R.family.path.levels.S i n) atTop:=
    cover_size R.family.path.levels.S i n
  filter_upwards [grow.eventually_ge_atTop (2*breadth J o origin base+1)] with u enough
  let X:=side u
  have h:n.val∣X.val:=u.prop
  obtain ⟨fits,limit⟩:=ready n X pay h
  have large:n.val≤X.val:=Nat.le_of_dvd X.pos h
  have chart:2*breadth J o origin base<X.val:=by simpa only [Nat.add_one_le_iff] using enough
  have placed:=(WilsonNeutralTwoPrintPathBoxHome.original h J o origin base chart).1
  have zero:=(WilsonNeutralTwoPrintPathBoxHome.original h J o 0 base (by omega)).2
  have span(v:J.erase o):separation (wrap X origin) (homes X origin base v)≤d:=by
    calc
      _ = separation (wrap X 0) (homes X 0 base v):=by
        simp only [homes,map_add,map_zero,zero_add]
        rw [add_comm (wrap X origin)]
        simpa only [zero_add] using (separation_translate 0 (wrap X (base v)) (wrap X origin))
      _ ≤ d:=(zero v).trans near
  have upper:=WilsonOriginalCensusCanonicalPeriod.finite R k κ pt simple N i great seed cells J o active a r hs
    (hire N great seed cells) h (wrap X origin) (homes X origin base) d span
    (lt_of_lt_of_le fits large) test weights H hp bounded
  dsimp only at upper
  rw [placed] at upper
  have scale (z:ℝ):z*(‖test‖*H)≤ |z| * cap:=
    (mul_le_mul_of_nonneg_right (le_abs_self z) (mul_nonneg test.opNorm_nonneg hp)).trans
      (mul_le_mul_of_nonneg_left budget (abs_nonneg z))
  have cost:(Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*price J o (Hooks G) r σ (‖test‖*C)+
        ‖test‖*(tariff (Hooks G) r σ C*catchW (σ/512) X))*H =
      Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*(A*(‖test‖*H))+
        (B*(‖test‖*H))*catchW (σ/512) X:=by
    unfold A B WilsonNeutralTwoPrintPathPageLedger.price WilsonNeutralTwoPrintPathRankFare.tariff
    ring
  exact upper.trans (cost.le.trans ((add_le_add (mul_le_mul_of_nonneg_left (scale A) (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_right (scale B) (show 0≤catchW (σ/512) X from (Real.exp_pos _).le))).trans (by simpa only [zero_mul,add_zero] using limit)))

end YM.Integration.WilsonIndependentCollarCanonicalRelativeRank
end

