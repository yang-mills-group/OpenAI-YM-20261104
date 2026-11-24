import YM.Integration.WilsonOriginalCensusPhysicalWinding
import YM.Integration.WilsonNeutralTwoPrintPathTariff

/-! A genuine finite side is chosen for the lower reference. Both finite
Wilson conditionals use their own dated vacuum at the very same cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiniteWinding
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

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open WilsonOriginalCensusOrbitCenters (layout shifted)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)
open scoped Classical BigOperators
variable {G:Gauge}{e v:ℕ}{D k:Fin v→ℕ}{I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}

theorem original (Q:Realm G (e+1) Credit.leanC)(m:ℕ)(admit:Q.anchor ≤ m)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)
    (J:Finset I)(a r:ℕ)(grade:a ≤ e){s:ℝ}(width:0<s):
    ∃C σ C₀ σ₀:ℝ,0 ≤ C ∧ 0<σ ∧ 0 ≤ C₀ ∧ 0<σ₀ ∧ ∀N,m<N → ∀(n X:Side)(h:n.val∣X.val)
      (Y:Outerm G D)(B:ℝ),1 ≤ B → Wellness k Y → CoverBill Y e s B →
      ∀(sites:I→Fin v → Cover)(read:(i:I)→Pen D (words i) →L[ℝ] Vote (H i))
       (b:I→Site (loose Q.draws m).L)(o:I)(_live:o∈J)(root:Site X)(site:(J.erase o)→Site X)
       (d:ℕ), (∀j,separation root (site j) ≤ d) → 32*d<n.val →
      ∀(test:Pen H J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)(height:ℝ),
      0 ≤ height → (∀x,‖weights x‖ ≤ height) →
      let salary:=amount B words read
      let previous:=gathered Y k e words front sites read
      let mass₀:=fun i=>mass k (words i)
      let pos:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)=>layout h J o (w.val+root) (shifted h site w)
      let row:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)(p:(J.erase o)→Fin (Pages n X))=>
        high mass₀ e Q.draws Q.paid N m X J previous (pos w p) b a r
      let plotted:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)=>∑x:Fin r→Site X × Hooks G,
        (∑p,test (row w p x))*weights (WilsonNeutralTwoPrintPathPageRead.lower h ∘ x)
      let y₀:=layout h J o root site (retained h site)
      let central:=∑y:Fin r→Site n × Hooks G,
        test (high mass₀ e Q.draws Q.paid N m n J previous y₀ b a r y)*weights y
      ‖mean h plotted-central‖ ≤
        (Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*price J o (Hooks G) r σ (‖test‖*(C*salary^J.card))+
          ‖test‖*(tariff (Hooks G) r σ (C*salary^J.card)*catchW (σ/512) X))*height+
        ‖test‖*(tariff (Hooks G) r σ₀ (C₀*salary^J.card)*catchW (σ₀/512) n)*height:=by
  obtain ⟨C,σ,hC,hσ,sold⟩:=WilsonOriginalCensusPhysicalWinding.original (k:=k) (H:=H)
    Q m admit words front named J a r grade width
  obtain ⟨C₀,σ₀,Cpos,σpos,cash⟩:=WilsonNeutralTwoPrintPathTariff.submitted
    (D:=H) (k:=fun i=>mass k (words i)) Q m admit J a r grade width
  refine ⟨C,σ,C₀,σ₀,hC,hσ,Cpos,σpos,?_⟩
  intro N live n X h Y B base well bill sites read b o active root site d near room test weights height hp bounded
    salary previous mass₀ pos row plotted y₀ central
  let F:=(logO Q.draws Q.paid m N
    (submit previous mass₀ e (chartIn (loose Q.draws m) y₀ b)) mass₀ J).2 a r
  let fixed:=∑y:Fin r→Site n × Hooks G,test (plume F n y)*weights y
  have large:n.val≤X.val:=Nat.le_of_dvd X.pos h
  have upper:‖mean h plotted-fixed‖≤_:=sold N live n X h Y B base well bill sites read
    b o active root site d near (lt_of_lt_of_le room large) test weights height hp bounded
  have inc:=WilsonNeutralTwoPrintPathInheritedBlocks.original Y well width base bill words front named sites read
  have current:=cash N live n previous salary inc.1 inc.2.1 inc.2.2 y₀ b
  have apart:4*crestCard y₀ J<n.val:=by
    have bound:=WilsonPointChildRelativeLift.radius h J o root site d near
    dsimp only [y₀,layout]
    omega
  let K:=high mass₀ e Q.draws Q.paid N m n J previous y₀ b a r
  have radius:(∑y,‖K y-plume F n y‖)≤tariff (Hooks G) r σ₀ (C₀*salary^J.card)*catchW (σ₀/512) n:=
    WilsonNeutralTwoPrintPathRankFare.original ⟨o,active⟩ apart σpos current
  have lower:‖central-fixed‖≤‖test‖*(tariff (Hooks G) r σ₀ (C₀*salary^J.card)*catchW (σ₀/512) n)*height:=by
    change ‖(∑y,test (K y)*weights y)-∑y,test (plume F n y)*weights y‖≤_
    rw [←Finset.sum_sub_distrib]
    simp_rw [←sub_mul,←map_sub]
    calc
      _ ≤ ∑y,‖test (K y-plume F n y)*weights y‖:=norm_sum_le _ _
      _ ≤ ∑y,‖test‖*‖K y-plume F n y‖*height:=Finset.sum_le_sum fun y _=> by
        rw [norm_mul]
        exact mul_le_mul (test.le_opNorm _) (bounded y) (norm_nonneg _) (mul_nonneg test.opNorm_nonneg (norm_nonneg _))
      _ ≤ _:=by
        rw [←Finset.sum_mul,←Finset.mul_sum]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left radius test.opNorm_nonneg) hp
  exact (norm_sub_le_norm_sub_add_norm_sub (mean h plotted) fixed central).trans (add_le_add upper (by
    rwa [norm_sub_rev] at lower))

end YM.Integration.WilsonOriginalCensusFiniteWinding
end
