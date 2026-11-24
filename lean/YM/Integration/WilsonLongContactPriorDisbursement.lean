import YM.Integration.WilsonLongContactPriorGenerated
import YM.Integration.WilsonLongContactPriorRemittance
import YM.Integration.WilsonLongContactPriorScale

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorDisbursement
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

theorem entered {α:Type} [DecidableEq α] [Fintype α] {Γ:Marker.Census α} {seats:α→Site f}
    (roster:ι→Menu.Hat Γ R) (g:α→ℝ) (hw:∀i,0<g i) (cost:ℝ)
    (old:Menu.Offer seats roster g R.p.B R.p.supportExponent cost) {i:ℕ}
    (reserve:(Fintype.card α:ℝ)*cost≤betaF G x L)
    (paid:WilsonLongContactPriorRemittance.Booked P Q L μ i x)
    (visit:Bikes Q L μ x a L' B j n):
    let names:=fun k=>(roster k).M
    let l:=fun k=>Menu.sumFee (roster k) g
    Palette.Plot names H (mulScale ((tax G L x)⁻¹) l):=by
  intro names l
  have hR:radiusCost Q L R.p.supportExponent:=H.laws.intake.exponent ▸ paid.1
  have hB:R.p.B≤2*radiusB x:=by
    rw [H.laws.intake.sizes,H.laws.data.funds.length_eq]
    exact visit.covers
  have sc:=WilsonLongContactPriorScale.roster (S:=S) seats roster g hw cost old
  obtain ⟨pos,_,cash⟩:=habitats names H l sc paid.2.1 hB hR
  exact plot_built names H _ pos (fun t=>budget_loosen (cash t) (paid.2.2.1 (Fintype.card α) cost reserve))

include N hx he
theorem original {α:Type} [DecidableEq α] [Fintype α] {Γ:Marker.Census α} {seats:α→Site f}
    (roster:ι→Menu.Hat Γ R) (g:α→ℝ) (hw:∀i,0<g i) (cost:ℝ)
    (old:Menu.Offer seats roster g R.p.B R.p.supportExponent cost) {i:ℕ}
    (reserve:(Fintype.card α:ℝ)*cost≤betaF G x L)
    (paid:WilsonLongContactPriorRemittance.Booked P Q L μ i x)
    (visit:Bikes Q L μ x a L' B j n) (hk:k ≤ i) (hs:s ≤ i):
    let names:=fun t=>(roster t).M
    let l:=fun t=>Menu.sumFee (roster t) g
    let D:Match.Alliance H H 1 0:=Match.staple rfl rfl rfl
    ∃ cash:ℕ→Finset ι→ℝ, (∀i p,0≤cash i p ∧ ∀U,‖cod names H χ l H D i U p‖≤cash i p) ∧
      Ac.Hit (fun i=>((Beam.marquee H V).hard i).support) V.B
        (fun i=>∑p:Finset ι,if p.card≤k then cash i p else 0) a ((gStep R.beta)^s):=by
  intro names l D
  have listed:=entered H roster g hw cost old reserve paid visit
  obtain ⟨C₀,pos,fee⟩:=WilsonLongContactPriorGenerated.original (k:=k) names H χ l N H D V
    (Beam.marquee H V).reg (Height.serve H D χ (Beam.lit H)).logRead hx he visit listed paid.2.1
  obtain ⟨lo,hi⟩:=H.laws.intake.window
  have top:=H.laws.intake.height
  rw [H.laws.data.funds.length_eq] at lo hi top
  have band:inBand (betaF G x L) R.beta:=⟨by linarith only [lo,top],by linarith only [hi,top]⟩
  have quote:=paid.2.2.2 k hk s hs R.beta band
  have hT:0≤(tax G L x)^k:=pow_nonneg (zero_le_one.trans (one_le_pow₀ paid.2.1)) k
  have smaller:Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)≤Real.exp (-Q.mark L μ x):=by
    calc _ ≤ Real.exp (-Q.mark L μ x)*1:=mul_le_mul_of_nonneg_left (by linarith only [visit.gains]) (Real.exp_pos _).le
         _ = _:=mul_one _
  exact ⟨C₀,pos,fun z=>budget_loosen (fee z) ((mul_le_mul_of_nonneg_left smaller hT).trans quote)⟩

end YM.Integration.WilsonLongContactPriorDisbursement
