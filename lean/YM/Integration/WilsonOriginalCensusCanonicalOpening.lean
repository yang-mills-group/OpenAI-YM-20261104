import YM.Integration.WilsonOriginalCensusCanonicalPeriod
import YM.Integration.WilsonOriginalCensusOrbitPeriod

/-! A period tail, chosen before the UV cutoff and the basis input, controls the
complete relative-copy reading from the first canonical step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalOpening
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
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonNeutralTwoPrintPathBoxPlacement (homes)
open scoped Classical BigOperators Topology

def central (N i:ℕ)(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
    (J:Finset I)(o:I)(a r:ℕ)(n:Side)(origin:Cover)(base:(J.erase o) → Cover)
    (test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ):ℂ:=
  ∑z,test (Actual R k κ pt N i seed cells J a r n (ink J o origin base) z)*weights z

def copyRead (N i:ℕ)(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
    (J:Finset I)(o:I)(a r:ℕ)(n X:Side)(h:n.val∣X.val)(origin:Cover)(base:(J.erase o) → Cover)
    (test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ):ℂ:=
  mean h (plotted h J o (wrap X origin) (homes X origin base) (Actual R k κ pt N i seed cells J a r X) test weights)

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀(J:Finset I)(o:I),o∈J → ∀a r,a≤Q → ∀d (cap ε:ℝ),0<ε →
    ∀ᶠ per:ℕ in atTop,∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
      (n X:Side), (R.family.side i per).val∣n.val → ∀h:n.val∣X.val,∀(origin:Cover)(base:(J.erase o) → Cover),
      breadth J o origin base≤d → ∀(test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)
        (H:ℝ),0≤H → (∀x,‖weights x‖≤H) → ‖test‖*H≤cap →
      let fixed:=∑z:Fin r→Site n × Hooks G,
        test (plume (Covered R k κ pt N i seed cells J a r (ink J o origin base)) n z)*weights z
      ‖copyRead R k κ pt N i seed cells J o a r n X h origin base test weights-fixed‖ +
        ‖central R k κ pt N i seed cells J o a r n origin base test weights-fixed‖≤ε:=by
  filter_upwards [WilsonOriginalCensusCanonicalPeriod.issued R k κ pt simple sale paid Q] with i bought
  intro J o live a r grade d cap ε pos
  obtain ⟨C,σ,_,hs,income⟩:=bought J a r grade
  let A:=C*price J o (Hooks G) r σ 1
  let B:=C*tariff (Hooks G) r σ 1
  filter_upwards [WilsonOriginalCensusOrbitPeriod.cost R i d σ σ (|A| *cap) (|B| *cap) (|B| *cap) ε hs hs pos] with per ready
  intro N fine seed cells n X pay h origin base near test weights H hp bounded budget
  obtain ⟨fits,limit⟩:=ready n X pay h
  have large:n.val≤X.val:=Nat.le_of_dvd X.pos h
  obtain ⟨placed,span⟩:=WilsonNeutralTwoPrintPathBoxHome.original h J o origin base (by omega)
  let Y:=ink J o origin base
  let F:=Covered R k κ pt N i seed cells J a r
  let fixed:=∑z:Fin r→Site n × Hooks G,test (plume (F Y) n z)*weights z
  have wages:=income N fine seed cells
  have upper:=WilsonOriginalCensusCanonicalPeriod.finite R k κ pt simple N i fine seed cells J o live a r hs
    wages h (wrap X origin) (homes X origin base) d (fun v=>(span v).trans near)
    (lt_of_lt_of_le fits large) test weights H hp bounded
  dsimp only at upper
  rw [placed] at upper
  have geometry:4*crestCard Y J<n.val:=by
    have rad:=WilsonPointChildRelativeLift.radius h J o (wrap X origin) (homes X origin base) d (fun v=>(span v).trans near)
    change crestCard (layout h J o (wrap X origin) (homes X origin base) (retained h (homes X origin base))) J≤8*d at rad
    rw [placed] at rad
    dsimp only [Y]
    omega
  let K:=Actual R k κ pt N i seed cells J a r n Y
  have radius:(∑z,‖K z-plume (F Y) n z‖)≤tariff (Hooks G) r σ C*catchW (σ/512) n:=
    WilsonNeutralTwoPrintPathRankFare.original ⟨o,live⟩ geometry hs (wages n Y)
  have lower:‖central R k κ pt N i seed cells J o a r n origin base test weights-fixed‖≤
      ‖test‖*(tariff (Hooks G) r σ C*catchW (σ/512) n)*H:=by
    change ‖(∑z,test (K z)*weights z)-∑z,test (plume (F Y) n z)*weights z‖≤_
    rw [←Finset.sum_sub_distrib]
    simp_rw [←sub_mul,←map_sub]
    calc
      _ ≤ ∑z,‖test (K z-plume (F Y) n z)*weights z‖:=norm_sum_le _ _
      _ ≤ ∑z,‖test‖*‖K z-plume (F Y) n z‖*H:=Finset.sum_le_sum fun z _=>by
        rw [norm_mul]
        exact mul_le_mul (test.le_opNorm _) (bounded z) (norm_nonneg _) (mul_nonneg test.opNorm_nonneg (norm_nonneg _))
      _ ≤ _:=by
        rw [←Finset.sum_mul,←Finset.mul_sum]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left radius test.opNorm_nonneg) hp
  have scale(z:ℝ):z*(‖test‖*H)≤|z| * cap:=
    (mul_le_mul_of_nonneg_right (le_abs_self z) (mul_nonneg test.opNorm_nonneg hp)).trans
      (mul_le_mul_of_nonneg_left budget (abs_nonneg z))
  have algebra:
      (Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*price J o (Hooks G) r σ (‖test‖*C)+
        ‖test‖*(tariff (Hooks G) r σ C*catchW (σ/512) X))*H+
      ‖test‖*(tariff (Hooks G) r σ C*catchW (σ/512) n)*H =
      Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*(A*(‖test‖*H))+
        (B*(‖test‖*H))*catchW (σ/512) X+(B*(‖test‖*H))*catchW (σ/512) n:=by
    unfold A B WilsonNeutralTwoPrintPathPageLedger.price WilsonNeutralTwoPrintPathRankFare.tariff
    ring
  exact (add_le_add upper lower).trans (algebra.le.trans ((add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (scale A) (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_right (scale B) (Real.exp_pos _).le))
    (mul_le_mul_of_nonneg_right (scale B) (Real.exp_pos _).le)).trans limit))

end YM.Integration.WilsonOriginalCensusCanonicalOpening
end
