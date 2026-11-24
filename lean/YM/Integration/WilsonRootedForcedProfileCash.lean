import YM.Integration.WilsonRootedForcedProfile
import YM.Integration.WilsonLongContactPriorFullGas

/-! The complete physical submitted previous cover with one bounded scratch profile.
The old vacuum and the true regular exponential multiply the scratch coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedForcedProfileCash
open YM YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
open Daisy
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
open Height AnalyticBridge.VerifiedReset
variable {δ Gp:ℝ}
local notation "T'" => Q.costs L μ R.beta x q
local notation "λ₀" => mulScale ((tax G L x)⁻¹) l
local notation "F'" => Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)

open PhysicalNext.Repeat Mallow Merge.Photo Progress.DirectedRecipe
open Ovens
variable {R':Rep G f} (Y : Cash W x μ L Q o C T R') (D:Match.Alliance Y H 1 0) (V:BudgetPoint)
variable (hx: V.threshold=Pressure.temp x)(he:V.B=radiusB x)

open MergeProof

open Marker Switch GridRenewal.Rain
variable {α:Type} [DecidableEq α] [Fintype α] {Γ:Marker.Census α}

def Submitted (roster:ι→Menu.Hat Γ R) (g:α→ℝ) (fee:ℝ):Prop:=
  let M:=fun i=>(roster i).M
  let l:=fun i=>Menu.sumFee (roster i) g
  let mark:=fun i=>Menu.sing (roster i) g
  let D:Match.Alliance H H 1 0:=Match.staple rfl rfl rfl
  let slots:=(Beam.marquee H V).reg
  let readout:=(Height.serve H D χ (Beam.lit H)).logRead
  ∀(F:Tree.Forest S.ratio)(U:Config G c)(h:Site c→ℂ), (∀x,‖h x‖≤1)→
    let lyrics(z:H.fragrances):Poly Γ:=∑ v:Syllable M H z, if Turns M H z v then
      ((↑(invests M H z v l*cut M H χ z v U)):ℂ) • ∏i∈page M H z v,mark i else 0
    let vacuum:=overhead (prism T x χ o.K U F) R Q.table
    let hard:=fun i:ℕ=>∑ t:Finset ι, (↑(cod M H χ l H D i U t):ℂ) • ∏j∈t,mark j
    let fronts:=Photo.fronts (Refrain.read H D χ slots readout) hard U V
    let regular:=GridRenewal.Rain.cyclone (∑'z,lyrics z)
    let old:=Refrain.read H D χ slots readout
    let counted:=fun s:Finset ℕ=>(∑i∈s,h (WilsonRootedForcedProfile.seat old i)) • fronts s
    let money:=if (flags V.threshold U).Nonempty then fee else 0
    Summable lyrics ∧ Summable fronts ∧
      Comparison.RG02.Actual.Push S R.beta (Menu.Expense roster g S) U=(↑vacuum:ℂ) • (regular*∑'s,fronts s) ∧
      Summable counted ∧ Poly.price g (∑'s,counted s) ≤ money ∧
      Poly.price g ((↑vacuum:ℂ) • (regular*∑'s,counted s))≤‖(↑vacuum:ℂ)‖*Poly.price g regular*money
end YM.Integration.WilsonRootedForcedProfileCash

namespace YM.Integration.WilsonRootedForcedProfileCash
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

open RGLocalTaylor RGLocalTaylor.Laminate

open QLocalRequestedHeirPurchase WilsonCoherentMayerElection
open WilsonPositionSeparatedProfileMayerThermalElection (Sales)
open WilsonLongContactSectorProtection ManuscriptQLocalMarkedHeightRun

open WilsonMovingRoutedMayerStage
open RemainderComparison.Lyric Merge Merge.Palette
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}
variable {R:Run G} {J:Request V} {A:NumericSchedule R.family J} {d:LocalFormal.Datum R.family Γ}
    {F:AnalyticInput J A d} {η:ℝ} (I:FullPreparedInputAt F η) {book:Booking G}
    (H:WilsonRootedSubmittedTail.CashAt I book)

variable (J:Request V) (extra:Stage→ℕ→ℝ) (γ:ℝ) (ρ:Premium G J.outputFieldOrder)
    (test:Demand G) (R:Run G) (χ:Chi) (δ:Daisy.Charity.RG12.Decal G)
local notation "fees" => (WilsonLongContactPriorRemittance.decal G).paired δ
local notation "fees₁" => calendar G fees
local notation "Δ" => WilsonGaussianDeterminantTender.joined G J χ fees₁
variable (licensed:WilsonLongContactMayerBooking.Sold J
    (WilsonGaussianDeterminantTender.joined G J χ (calendar G ((WilsonLongContactPriorRemittance.decal G).paired δ))) extra γ ρ test R.kit) (A:NumericSchedule R.family J)


theorem purchased (simple:G.Simple) (p:ℕ) (ε:ℝ) (small:0<ε):
    ∀ᶠm:ℕ in atTop,∀(d:LocalFormal.Datum R.family Γ),d.level=m→
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I→
      let lev:=R.alloy.B.a
      let b:=licensed.choose (lev.clock.J (d.level+1)) (lev.clock.J d.level)
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀H:WilsonRootedSubmittedTail.CashAt I b,∀base field E K,
        let roster:=(ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base field E K).terms
        Submitted H Chi.canonical (A.outputNorm d.level) roster F.inputRadii (ε*g^p):=by
  classical
  have half:0<(1/2:ℝ):=by norm_num
  filter_upwards [WilsonLongContactPriorBank.purchased (Γ:=Γ) J extra γ ρ test R χ δ licensed A simple p (ε/2) (half_pos small),
    WilsonLongContactPriorBank.purchased (Γ:=Γ) J extra γ ρ test R χ δ licensed A simple 0 (1/2) half]
    with m high low d hm F η I cut
  intro lev b g H base y E K roster
  have tall:=high d hm F I cut H base y E K
  have flat:=low d hm F I cut H base y E K
  have haar:=WilsonLongContactPriorHaar.received H Chi.canonical (A.outputNorm d.level) roster F.inputRadii tall.1
  have hw:∀v,0<F.inputRadii v:=(rosterBudget I).radii
  intro forest U h cap
  obtain ⟨re,fa,identity⟩:=haar forest U
  let D:Match.Alliance H H 1 0:=Match.staple rfl rfl rfl
  let P:=A.outputNorm d.level
  let C:=PhysicalNext.Repeat.Refrain.read H D Chi.canonical (Beam.marquee H P).reg
    (Height.serve H D Chi.canonical (Beam.lit H)).logRead
  let names:=fun i=>(roster i).M
  let l:=fun i=>Menu.sumFee (roster i) F.inputRadii
  let hard:=WilsonLongContactPriorModes.hard roster F.inputRadii (fun i t=>cod names H Chi.canonical l H D i U t)
  let target:=min ((ε/2)*g^p) (1/2:ℝ)
  have ts:2*target≤1:=by linarith only [min_le_right ((ε/2)*g^p) (1/2:ℝ)]
  have paid:=WilsonRootedForcedProfile.profile C P F.inputRadii hard hw ts U (h:=h) (cap:=cap)
  have schedule:∀(x:Site (R.family.side d.level d.period))(selected:Finset ℕ),∑i∈Ac.buds (fun i=>(C.forced i).support) selected {x},Poly.price F.inputRadii (hard i)≤target:=by
    intro x selected
    have h:=(tall.2 {x} selected).1 U
    have z:=(flat.2 {x} selected).1 U
    have hx:((({x}:Finset (Site (R.family.side d.level d.period))).card:ℕ):ℝ)=1:=by exact_mod_cast Finset.card_singleton x
    apply le_min
    · exact h.trans_eq (congrArg (·*((ε/2)*g^p)) hx |>.trans (one_mul _))
    · exact z.trans_eq (congrArg (·*((1/2)*(g^0))) hx |>.trans (by rw [one_mul,pow_zero,mul_one]))
  have expense:=paid schedule
  have sw:(if (flags P.threshold U).Nonempty then 2*target else 0)≤(if (flags P.threshold U).Nonempty then ε*g^p else 0):=by
    split_ifs
    · linarith only [min_le_left ((ε/2)*g^p) (1/2:ℝ)]
    · exact le_rfl
  refine ⟨re,fa,identity,expense.1,expense.2.trans sw,?_⟩
  rw [Poly.adapted,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((Poly.multiplication hw _ _).trans
    (mul_le_mul_of_nonneg_left (expense.2.trans sw) (Poly.nonnegative hw _))) (norm_nonneg _)
end YM.Integration.WilsonRootedForcedProfileCash
