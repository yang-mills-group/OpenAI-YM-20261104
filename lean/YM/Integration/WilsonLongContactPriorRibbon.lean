import YM.RemainderComparison.Lyric.Forecast

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorRibbon
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


/-- The previously bought roster may use a full power of the true fine temperature. -/
theorem affordable (Q:ConnectedActivityE6.Target G P) (L:Side):
    ∀ᶠ x:ℝ in atTop,∀m:ℕ,∀p:ℝ,(m:ℝ)*p≤betaF G x L →
      ink Q L x m p ≤ Daisy.ribbon Q L x:=by
  have base:Rate G L ((-3/2):ℝ) (fun x=>ink Q L x 1 1):=
    ink_cost Q L (m:=fun _=>1) (by simpa only [Nat.cast_one] using (Rate.const (G:=G) (L:=L) 1)) (Rate.const 1)
  have β:Rate G L 1 (fun x=>betaF G x L):=by simpa only [Real.rpow_one] using (Rate.power (G:=G) (L:=L) (a:=1))
  have h:=((base.mul β).mul (Rate.power (a:=-Q.rate))).below (by linarith only [Q.start])
    (Real.exp (Q.relative*Footprint.preCost (Q.halo+5))) (Real.exp_pos _)
  filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 0,h] with x hx h
  intro m p hp
  have goal:0<(betaF G x L)^Q.rate:=Real.rpow_pos_of_pos hx _
  have div:= (le_abs_self _).trans h
  change ink Q L x 1 1*betaF G x L*(betaF G x L)^(-Q.rate) ≤ _ at div
  rw [Real.rpow_neg hx.le,←div_eq_mul_inv] at div
  have h' := (div_le_iff₀ goal).mp div
  change ink Q L x m p ≤ (betaF G x L)^Q.rate*_
  rw [mul_comm ((betaF G x L)^Q.rate)]
  apply le_trans _ h'
  have fee:0≤Extra.Multi.siteFactor (radiusB x) * Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) *
        (grow G L x*(tax G L x)⁻¹):=by unfold Extra.Multi.siteFactor tax Height.grow; positivity
  calc
    ink Q L x m p = (Extra.Multi.siteFactor (radiusB x)*Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5))*
      (grow G L x*(tax G L x)⁻¹))*((m:ℝ)*p):=by unfold ink;ring
    _ ≤ _:=mul_le_mul_of_nonneg_left hp fee
    _ = ink Q L x 1 1*betaF G x L:=by unfold ink;push_cast;ring

end YM.Integration.WilsonLongContactPriorRibbon
