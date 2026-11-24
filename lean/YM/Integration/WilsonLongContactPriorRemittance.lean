import YM.Integration.WilsonLongContactPriorRibbon
import YM.Integration.ManuscriptQLocalMarkedHeight

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorRemittance
open YM YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Next.Scheduling
open Merge Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)

open Daisy
local notation "X'" => Palette.mark M (c:=c)
local notation "Lk" => ConnectedActivityE6.lengths T R
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
open Height AnalyticBridge.VerifiedReset
variable {δ Gp:ℝ}
open Delay



open RemainderComparison

theorem forced (Q:ConnectedActivityE6.Target G P) (L:Side) {μ:ℝ} (hm:0<μ) (k s:ℕ):
    ∀ᶠ x:ℝ in atTop,∀β:ℝ,inBand (betaF G x L) β →
      (tax G L x)^k*Real.exp (-Q.mark L μ x)≤(gStep β)^s:=by
  let a:ℝ:=(3/8:ℝ)*5*(k:ℝ)
  have growth:Rate G L a (fun x=>(tax G L x)^k):=((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 5).pow k
  have departed:=Lyric.mark_force Q L hm (-(s:ℝ)/2-1-a) 1 zero_lt_one
  have h:Rate G L (a+(-(s:ℝ)/2-1-a)) (fun x=>(tax G L x)^k*Real.exp (-Q.mark L μ x)):=by
    simpa only [mul_one] using growth.mul departed
  filter_upwards [Access.exchange _ s (by linarith only) h] with x hx β hb
  exact (le_abs_self _).trans (hx β hb)

def Booked (P:Teller G) (Q:ConnectedActivityE6.Target G P) (L:Side) (μ:ℝ) (i:ℕ) (x:ℝ):Prop:=
  radiusCost Q L P.top.supportExponent ∧ 1≤Height.grow G L x ∧
  (∀m:ℕ,∀p:ℝ,(m:ℝ)*p≤betaF G x L → ink Q L x m p ≤ Daisy.ribbon Q L x) ∧
  ∀ k ≤ i, ∀ s ≤ i, ∀β:ℝ,inBand (betaF G x L) β → (tax G L x)^k*Real.exp (-Q.mark L μ x)≤(gStep β)^s

/-- One length is chosen before every sector, and all finite receipts precede the regulator. -/
def decal (G:Gauge):Charity.RG12.Decal G where
  rub P Q _ L _ μ _ _ i x:=Booked P Q L μ i x
  good P Q _:=by
    obtain ⟨b,sites⟩:=Lyric.bidLift (Q:=Q) (v:=P.top.supportExponent) (b:=Q.ε)
      (by linarith only [Q.grants.1,Q.usable]) Q.usable
    refine ⟨b,fun L hL W μ o h i _ _ hm=>?_⟩
    have quotes:∀ᶠx:ℝ in atTop,∀k:Fin (i+1),∀s:Fin (i+1),∀β:ℝ,inBand (betaF G x L) β →
        (tax G L x)^k.val*Real.exp (-Q.mark L μ x)≤(gStep β)^s.val:=
      eventually_all.mpr fun k=>eventually_all.mpr fun s=>forced Q L hm k.val s.val
    filter_upwards [WilsonLongContactPriorRibbon.affordable Q L,quotes,
      (Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hp hs g
    exact ⟨sites L hL,Real.one_le_rpow g (by norm_num),hp,
      fun k hk s hs' β hb=>hs ⟨k,Nat.lt_succ_of_le hk⟩ ⟨s,Nat.lt_succ_of_le hs'⟩ β hb⟩

end YM.Integration.WilsonLongContactPriorRemittance
