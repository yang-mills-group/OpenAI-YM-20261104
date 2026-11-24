import YM.Integration.OriginalCommonWindingMarket
import YM.Integration.WilsonLimitConstruction.FundedRunPacketSale

/-! The incoming width of the actual blocking step prices the signed
finite-to-cover winding of its entire original marked family. Its charged
Laurent sum uses the same strictly positive output radii as the packet sale. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedMarkedWindingPayment
open Function Filter Finset Set Lattice RG RG.Supply Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology BigOperators Classical
variable {G : Gauge} {v e m : ℕ} {R : Run G} (Γ : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)
local notation "D" => NativeMarkedAddressTokens.axes O
local notation "B" => Block Γ k e

def menu (derivative : B→ℕ) (b : B) : OriginalCommonWindingMarket.Row (Fin v) e :=
  .marked b.1.val.val ⟨owner Γ b.1,owner_mem Γ b.1⟩ b.2.1 b.2.2.val (derivative b)

theorem inlet {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m} {u : ℝ}
    (X : Input Q hm univ k (D) u) (S : Finset (Fin v)) (y : Fin v → Cover) :
    Eu k (X.familyAt y) ∧ X.familyAt y ∅=0 ∧
    safeB (chartIn (loose Q.draws m) y (X.offsets y)) (X.familyAt y) S e (Q.mint m hm).past u :=
  ⟨X.degree y,X.empty y,fun T _ i hi r=>(X.price y T (subset_univ _) i hi r).shave (Q.crossing m hm)⟩

variable {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m} {u : ℝ}

def RowInvoice (X : Input Q hm univ k (D) u) (cutoff period : ℕ)
    (c q : ℕ) (scale : B→Gear G→ℝ) (degree derivative : B→ℕ) (b : B) (bill : ℝ) : Prop :=
  let n := R.family.side m period
  let g := Pert.Asymptotics.regulatorRun R.family cutoff period (m+1)
  let I := (Q.mint m hm).gear
  let S := b.1.val.val
  let o := owner Γ b.1
  let x := fun z=>PeriodicMarkedWinding.roots n z o
  let cover := fun z=>((output X S cutoff (x z)).2 b.2.1.val b.2.2.val)
  let finite := fun z=>coilH Q.draws Q.paid m cutoff n (X.familyAt (x z)) k
    (ratioHigh Q.draws Q.paid cutoff m) S b.2.1.val b.2.2.val
  bill*g^(-(c:ℝ))≤g^q*u^S.card ∧
    bill≤ActualRunAdmissionScales.admittedCost R.family.path.levels m^(degree b)*
      (Real.exp (-(scale b I/512)*(n.val:ℝ))*u^S.card) ∧
    PostMark S o b.2.2.val (RootedPeriodicMarkedWinding.row n S o (fun z=>Carp.plume (cover z) n-finite z))
      (scale b I/32/2/2/2) bill (derivative b)

theorem item (X : Input Q hm univ k (D) u) (hu : 0≤u) (N p : ℕ) (hN : m<N)
    (c q : ℕ) (scale : B→Gear G→ℝ) (degree derivative : B→ℕ) (b : B)
    (paid : OriginalCommonWindingMarket.Receipt R (D) k c q (degree b)
      (fun I=>I.past) (scale b) m Q hm (menu Γ k derivative b)) :
    ∃ bill,RowInvoice Γ k O (R:=R) X N p c q scale degree derivative b bill :=
  paid N p hN X.familyAt X.offsets u hu (inlet k O X b.1.val.val)

private theorem principal (b : B) : 1≤OriginalRunMarkedPacketPurchase.majorant Γ k O R (m:=m) b := by
  unfold OriginalRunMarkedPacketPurchase.majorant NativeMarkedAddressTokens.cellPrice
  apply one_le_mul_of_one_le_of_one_le
  · apply Finset.one_le_prod
    intro x _
    apply one_le_pow₀
    norm_num
  · apply one_le_pow₀
    exact ActualRunAdmissionScales.admittedCost_one _ _

variable {J : Request (Fin v)} {A : NumericSchedule R.family J} {d : LocalFormal.Datum R.family Γ}

theorem portfolio (F : AnalyticInput J A d) (u g room : ℝ) (hu : 0≤u) (hg : 0<g) (hr : 0<room)
    (q c : ℕ) (bill : B→ℝ) (paid : ∀b,bill b*g^(-(c:ℝ))≤g^q*u^b.1.val.val.card)
    {z : ℝ} (hz : g≤z) (hz1 : z≤1) :
    let F₀ := FundedRunPacketSale.funded Γ k O R m (e:=e) F u g room hg hr
    let w := fun x=>F₀.outputRadii x/F.kernelCosts x
    ∑b,Poly.toll w b.1.val*‖(z:ℂ)^(power Γ k e b)‖*(bill b*g^(-(c:ℝ)))≤g^q*room := by
  classical
  let cash := FundedRunPacketSale.expense Γ k O R m (e:=e) u
  let F₀ := FundedRunPacketSale.funded Γ k O R m (e:=e) F u g room hg hr
  let w := fun x=>F₀.outputRadii x/F.kernelCosts x
  let weight := fun b : B=>Poly.toll w b.1.val*‖(z:ℂ)^(power Γ k e b)‖
  have wh (i) : 0<w i := div_pos (F₀.output_radius_positive i) (F.kernel_positive i)
  have nn (b : B) : 0≤weight b := mul_nonneg (Poly.worth wh b.1.val).le (norm_nonneg _)
  have law (b : B) : b.2.2.val≤b.2.1.val+∑i∈b.1.val.val,k i := by
    have bound := b.2.2.isLt
    change b.2.2.val<(∑i∈b.1.val.val,k i)+b.2.1.val+1 at bound
    omega
  have sold := FundedLaurentSale.portfolio cash room F g 1 k hg zero_lt_one hr hz hz1
    (fun b : B=>b.1.val) (fun b=>b.1.property) (fun b=>b.2.1.val) (fun b=>b.2.2.val) law
  have total : ∑b,weight b*cash b≤room := by
    simpa only [weight, w, F₀, FundedRunPacketSale.funded, cash, power, one_pow, mul_one] using sold
  change ∑b,weight b*(bill b*g^(-(c:ℝ)))≤g^q*room
  calc _ ≤ ∑b,g^q*(weight b*cash b) := by
         apply Finset.sum_le_sum
         intro b _
         have lower : u^b.1.val.val.card≤cash b :=
           le_mul_of_one_le_left (pow_nonneg hu _) (principal Γ k O (R:=R) (m:=m) b)
         calc _≤weight b*(g^q*cash b) := mul_le_mul_of_nonneg_left
                ((paid b).trans (mul_le_mul_of_nonneg_left lower (pow_nonneg hg.le _))) (nn b)
              _=g^q*(weight b*cash b) := by ring
       _=g^q*(∑b,weight b*cash b) := (Finset.mul_sum ..).symm
       _≤_ := mul_le_mul_of_nonneg_left total (pow_nonneg hg.le _)

end YM.Integration.WilsonLimitConstruction.FundedMarkedWindingPayment
end
