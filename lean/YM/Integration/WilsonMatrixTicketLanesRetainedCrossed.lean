import YM.Integration.WilsonMatrixTicketLanesRetainedPairMoments
import YM.Integration.WilsonMatrixTicketLanesReflectedPropagator

/-! The physical conditional connected term of two graded quadratic angular words. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedCrossed
open Function Filter Lattice Gauge RG Tree Wilson Precision PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Chart PertExtension.GaussianScore RGComparison.Core16 RGComparison.Core16.Spool
open RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open RGComparison.Core16.Forge RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven RGComparison.Core16.Silk FVA2 FVA2.CityHistory
open FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Papers PowerSeries
open WilsonMatrixTicketLanesReflectedInner WilsonMatrixTicketLanesRetainedAngular WilsonMatrixTicketLanesReportedWords
open WilsonMatrixTicketLanesReportedPrepaid WilsonConditionalTaylorThermalCensus WilsonMatrixTicketLanesRetainedBid
open scoped Topology BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (Γ : Law E) (a b c d : Module.Dual ℝ E) (s : E)

def cross : ℝ := Γ.wick c b*Γ.wick d a + Γ.wick c a*Γ.wick d b +
  a s*c s*Γ.wick d b + a s*d s*Γ.wick c b + b s*c s*Γ.wick d a + b s*d s*Γ.wick c a

variable {G : Gauge} {c f : Side} (S : StepData c f) (T : Forest S.ratio) (large : Bid.Larger (G:=G) S)
   (tag : S.Choices) (nil : (Descent.nil (top:=f)).Tags) (u : Directions G c)
local notation "Γ₀" => law S T large tag nil
local notation "kept" => changeField S T large tag nil u
local notation "axes" => axis (G:=G) S T

variable {P : Parcel.Oven S.patch} (X : P.Form G) (offer : P.Offers X S.kernel) (pin : ∀ e,‖u e‖≤X.Q)
local notation "O" => Spool.lens (S:=S) u X T

include offer pin in
theorem mean (i : Wire G T.Free) : nth 0 (Silk.price O [i])=(axes i) kept := by
  let μ:=tangent G T.Free
  let B:=opening μ Γ₀
  let e:=coordinate S T i
  have z : B e=0:=by
    change (Γ₀).average μ (fun y=>(axes i) y)=0
    have base:= (Γ₀).recursion μ (axes i) (fun _:Unit=>axes i) (∅:Finset Unit)
    simpa only [Law.product,Finset.prod_empty,one_mul,Finset.sum_empty] using base
  have price := B.map_add e ((axes i kept)•1)
  rw [B.map_smul,starts,z,smul_eq_mul,mul_one,zero_add] at price
  rw [moment S T X offer large tag nil u pin]
  change (Γ₀).average μ (fun y=>(y+kept) i.1 i.2*1)=_
  change (Γ₀).average μ (fun y=>y i.1 i.2+kept i.1 i.2*1)=_ at price
  simpa only [Pi.add_apply,PiLp.add_apply,mul_one] using price

include offer pin in
/-- The two separate measured singleton means are subtracted before any norm. -/
theorem signed (i j h l : Wire G T.Free) : nth 0 (Silk.gap O [h,l] [i,j]) =
    cross Γ₀ (axes i) (axes j) (axes h) (axes l) kept := by
  change coeff 0 (_-_*_)=_
  simp only [coeff_zero_eq_constantCoeff_apply,map_sub,map_mul]
  simp only [←coeff_zero_eq_constantCoeff_apply]
  change nth 0 (Silk.price O [i,j,h,l])-nth 0 (Silk.price O [i,j])*nth 0 (Silk.price O [h,l])=_
  simp only [moment S T X offer large tag nil u pin,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  have got:=WilsonMatrixTicketLanesRetainedPairMoments.quadratic Γ₀ (tangent G T.Free) (axes i) (axes j) (axes h) (axes l) kept
  have coord (w : Wire G T.Free) (y : Future G S T) : axes w y=y w.1 w.2:=rfl
  simpa only [mul_assoc,cross,coord] using got

variable (R : Run G) (b : ℕ)
local notation "clockAt" p => R.family.path.levels.clock.op b p

/-- Price of every genuine conditional angular mean on this reporting scale, fixed before the
upper period and every choice of angular coordinate, forest, tag and retained field. -/
theorem bounded (paid : Paid G R.kit) (cap : ℕ) : ∀ᶠ b : ℕ in atTop,
    ∃ C : ℝ,0≤C ∧ ∀ p,∀ (T : Forest (R.family.path.levels.clock.op b p).ratio)
      (large : Bid.Larger (G:=G) (R.family.path.levels.clock.op b p))
      (tag : (R.family.path.levels.clock.op b p).Choices) (nil : (Descent.nil (top:=R.family.side (b+1) p)).Tags)
      (u : Directions G (R.family.side b p)),(∀ e,‖u e‖≤(cap:ℝ)+1)→∀ i : Wire G T.Free,
      |axis (R.family.path.levels.clock.op b p) T i (changeField (R.family.path.levels.clock.op b p) T large tag nil u)|≤C := by
  let empty : Menu G:=code (n:=0) (fun _=>0) (fun i=>i.elim0) 0 cap
  filter_upwards [paid.2 empty] with b sale
  obtain ⟨P,X,U,K,offer,width,rest⟩:=sale
  refine ⟨Silk.blank X offer.good 0 1,Silk.blank_nn ..,?_⟩
  intro p T large tag nil u inside i
  have pin (e) : ‖u e‖≤X.Q:=by rw [width];exact inside e
  have steady := Oven.paints T offer pin large
  have rate:=Silk.coupon offer.good steady 0 1 0 (le_refl _) (w:=[i]) (show [i].length≤1 from le_rfl)
  change |nth 0 (Silk.price (Spool.lens (S:=R.family.path.levels.clock.op b p) u X T) [i])|≤_ at rate
  rwa [mean (R.family.path.levels.clock.op b p) T large tag nil u X offer pin] at rate

end YM.Integration.WilsonMatrixTicketLanesRetainedCrossed
