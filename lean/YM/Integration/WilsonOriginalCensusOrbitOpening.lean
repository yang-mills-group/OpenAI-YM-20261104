import YM.Integration.WilsonOriginalCensusOrbitPeriod
import YM.Integration.WilsonMarkedIndependentMixedOrderedWinding

/-! Both physical finite-board windings and the relative orbit aperture
vanish on a single opening chosen before the physical ultraviolet cutoff,
including on every further auxiliary multiple of the physical period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusOrbitOpening
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


open Filter WilsonCoeffUV.Winding
open scoped Topology

def Heard (R:Run G)(Q:Realm G (e+1) Credit.leanC)(m:ℕ)
    (words:I → Finset (Fin v))(front:I → Fin v)(J:Finset I)(a r:ℕ)(s:ℝ)(o:I)
    (d:ℕ)(cap ε:ℝ)(per:ℕ):Prop:=
  ∀N,m<N → ∀(n X:Side), (R.family.side m per).val∣n.val → ∀h:n.val∣X.val,
      ∀(Y:Outerm G D)(B:ℝ),1 ≤ B → Wellness k Y → CoverBill Y e s B →
      ∀(sites:I→Fin v → Cover)(read:(i:I)→Pen D (words i) →L[ℝ] Vote (H i))
       (b:I→Site (loose Q.draws m).L)(root:Site X)(site:(J.erase o)→Site X), (∀j,separation root (site j) ≤ d) →
      ∀(test:Pen H J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)(height:ℝ),
      0 ≤ height → (∀x,‖weights x‖ ≤ height) →
      ‖test‖*(amount B words read)^J.card*height ≤ cap →
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
      ‖mean h plotted-central‖ ≤ ε

theorem original (R:Run G)(Q:Realm G (e+1) Credit.leanC)(m:ℕ)(admit:Q.anchor ≤ m)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)
    (J:Finset I)(a r:ℕ)(grade:a ≤ e){s:ℝ}(width:0<s)
    (o:I)(live:o∈J)(d:ℕ)(cap ε:ℝ)(small:0<ε):
    ∀ᶠ per:ℕ in atTop, Heard (k:=k) (H:=H) (D:=D) R Q m words front J a r s o d cap ε per:=by
  obtain ⟨C,σ,C₀,σ₀,hC,hs,hC₀,hs₀,issued⟩:=WilsonOriginalCensusFiniteWinding.original
    (D:=D) (k:=k) (H:=H) Q m admit words front named J a r grade width
  let A:=C*price J o (Hooks G) r σ 1
  let B₁:=C*tariff (Hooks G) r σ 1
  let B₂:=C₀*tariff (Hooks G) r σ₀ 1
  filter_upwards [WilsonOriginalCensusOrbitPeriod.cost R m d σ σ₀ (|A| * cap)
    (|B₁| * cap) (|B₂| * cap) ε hs hs₀ small] with per ready
  intro N later n X physical multiple Y B Bpos law money sites read b root site distances test weights height hp bounded budget
  obtain ⟨fits,window⟩:=ready n X physical multiple
  have paid:=issued N later n X multiple Y B Bpos law money sites read b o live root site d distances fits test weights height hp bounded
  dsimp only at paid ⊢
  let gross:=‖test‖*(amount B words read)^J.card*height
  have positiveB:0≤B:=by linarith
  have positiveMass:0≤amount B words read:=by unfold amount; positivity
  have positiveGross:0≤gross:=by unfold gross; positivity
  have scale (z:ℝ):z*gross ≤ |z| * cap:=
    (mul_le_mul_of_nonneg_right (le_abs_self z) positiveGross).trans
      (mul_le_mul_of_nonneg_left budget (abs_nonneg _))
  have algebra:
      (Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*price J o (Hooks G) r σ (‖test‖*(C*(amount B words read)^J.card))+
        ‖test‖*(tariff (Hooks G) r σ (C*(amount B words read)^J.card)*catchW (σ/512) X))*height+
        ‖test‖*(tariff (Hooks G) r σ₀ (C₀*(amount B words read)^J.card)*catchW (σ₀/512) n)*height =
      Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*(A*gross)+
        (B₁*gross)*catchW (σ/512) X+(B₂*gross)*catchW (σ₀/512) n:=by
    unfold A B₁ B₂ gross WilsonNeutralTwoPrintPathPageLedger.price WilsonNeutralTwoPrintPathRankFare.tariff
    ring
  exact paid.trans (algebra.le.trans ((add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (scale A) (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_right (scale B₁) (Real.exp_pos _).le))
    (mul_le_mul_of_nonneg_right (scale B₂) (Real.exp_pos _).le)).trans window))


theorem collar (R:Run G)(days:Finset ℕ)(Q:(j:days) → Realm G (e+1) Credit.leanC)
    (admits:∀j,(Q j).anchor ≤ j.val)(words:I → Finset (Fin v))(front:I → Fin v)
    (named:∀l,front l ∈ words l)(kmax:ℕ)(strip:days → ℝ)(width:∀j,0<strip j)
    (aperture:days → ℕ)(cap ε:ℝ)(small:0<ε):
    ∀ᶠ per:ℕ in atTop,∀j:days,∀J:Finset I,∀o:J,∀a:Fin (e+1),∀r:Fin (kmax+1),
      Heard (k:=k) (H:=H) (D:=D) R (Q j) j.val words front J a.val r.val (strip j) o.val (aperture j) cap
        (ε/(1+(days.card*2^Fintype.card I*Fintype.card I*(e+1)*(kmax+1):ℕ):ℝ)) per:=by
  refine eventually_all.2 fun j=>eventually_all.2 fun J=>eventually_all.2 fun o=>
    eventually_all.2 fun a=>eventually_all.2 fun r=>?_
  exact original (D:=D) (k:=k) (H:=H) R (Q j) j.val (admits j) words front named J a.val r.val
    (by omega) (width j) o.val o.property (aperture j) cap _ (div_pos small (by positivity))

end YM.Integration.WilsonOriginalCensusOrbitOpening
end
