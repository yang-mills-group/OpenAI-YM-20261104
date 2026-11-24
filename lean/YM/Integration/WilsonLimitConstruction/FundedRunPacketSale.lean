import YM.Integration.OriginalRunMarkedPacketPurchase
import YM.Integration.WilsonLimitConstruction.FundedLaurentSale
import YM.Integration.WilsonLimitConstruction.FundedNativePacketGeometry

/-! Fixed on the source-funded original Run, all regulator and bare
readouts of the canonical packet bank share its one pre-period polynomial
radius tariff and genuine original output support. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedRunPacketSale
open Function Filter Finset Set MeasureTheory Lattice RG RG.Supply Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology BigOperators Classical

variable {G : Gauge} {v e : ℕ} (Γ : Census (Fin v)) (k : Fin v → ℕ) (O : Fin v → Orbit)
    (R : Run G) (m : ℕ)
local notation "D" => NativeMarkedAddressTokens.axes O
local notation "B" => Block Γ k e

def expense (amplitude : ℝ) (b : B) : ℝ :=
  OriginalRunMarkedPacketPurchase.majorant Γ k O R (m:=m) b * amplitude^b.1.val.val.card

variable {J : Request (Fin v)} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} (F : AnalyticInput J A d)
    (amplitude g room : ℝ) (hg : 0<g) (hr : 0<room)

def funded := FundedLaurentSale.funded (expense Γ k O R m (e:=e) amplitude) room F g 1 k hg zero_lt_one hr

local notation "F₀" => funded Γ k O R m (e:=e) F amplitude g room hg hr
local notation "w₀" => fun v => (F₀).outputRadii v/F.kernelCosts v

theorem upper (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (hA : 0 ≤ amplitude)
    (ticket : Insure v (mass k univ) Q Credit.leanC)
    (earned : ∀b:B,Q.cash (OriginalRunMarkedPacketPurchase.credit Γ k O (G:=G) b) m ≤ 
      ActualRunAdmissionScales.admittedCost R.family.path.levels m^
        ((OriginalRunMarkedPacketPurchase.credit Γ k O (G:=G) b).d+1))
    {z : ℝ} (hz : g ≤ z) (hz1 : z ≤ 1) :
    OriginalFundedMarkedPackets.budget Γ k O Q hm (A:=amplitude) (w₀) z ≤ room := by
  let out := expense Γ k O R m (e:=e) amplitude
  have f (b : B) : b.2.2.val ≤ b.2.1.val+∑j∈b.1.val.val,k j := by
    have t := b.2.2.isLt
    change b.2.2.val<(∑j∈b.1.val.val,k j)+b.2.1.val+1 at t
    omega
  have raw := FundedLaurentSale.portfolio out room F g 1 k hg zero_lt_one hr hz hz1
    (fun b : B=>b.1.val) (fun b=>b.1.property) (fun b=>b.2.1.val) (fun b=>b.2.2.val) f
  have hw (i) : 0<(w₀) i := div_pos ((F₀).output_radius_positive i) (F.kernel_positive i)
  calc _ ≤ ∑b:B,Poly.toll (w₀) b.1.val*‖(z:ℂ)^(power Γ k e b)‖*out b := by
         apply Finset.sum_le_sum
         intro b _
         exact mul_le_mul_of_nonneg_left
           (OriginalRunMarkedPacketPurchase.row Γ k O R Q hm amplitude hA ticket earned b)
           (mul_nonneg (Poly.worth hw b.1.val).le (norm_nonneg _))
       _ ≤ room := by simpa only [funded,one_pow,mul_one,power,out] using raw

def Stage (J : Request (Fin v)) : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.anchor=m ∧ Q.y=zz R.family.path.levels ∧
    Cloze (D) k Q Credit.leanC ∧ Insure v (mass k univ) Q Credit.leanC ∧
    (∀ j,m ≤ j → ∀ hj : Q.anchor ≤ j, ∃ five : 5 ≤ R.family.path.levels.clock.J (j+1),
      (Q.mint j hj).σ=crestM R.family.path.levels j five) ∧
    ∀ N,m<N → ∀ amplitude (X : Input Q hm univ k (D) amplitude), 0 ≤ amplitude  → 
    ∃ M : RootedMeasures Γ k O (e:=e) (G:=G),rootedSale Γ k O Q hm X (N:=N) M ∧
      ∀ (A : NumericSchedule R.family J) (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d),
      d.level=m → ∀ g room (hg : 0<g) (hr : 0<room),
      let out := funded Γ k O R m (e:=e) F amplitude g room hg hr
      ∀ (n : Side) (p : Fin v → Site n) (Y : Fin v → Dip), (∀i,(Y i).Fits (O i).field)  → 
        let P := OriginalFundedMarkedPackets.packets Γ k p O Y Q hm X (N:=N) (sampled Γ k p O M)
        ∀z,g ≤ z → z ≤ 1  → 
        P.Paid (A.outputNorm m) (fun i=>{p i}) (OriginalMeasuredSourceRows.region O Y (fun i=>{p i}))
          (fun i=>out.outputRadii i/F.kernelCosts i) z (width k Q hm) room
          (OriginalFundedMarkedPackets.offset k (e:=e)) 1

theorem selected (J : Request (Fin v)) (hG : G.Simple) (income : ℕ → Gear G → ℝ)
    (donor : FundedMarkedCoverRows.prices income R.kit) (hgrade : ∀i,k i<(D) i) :
    ∀ᶠ m : ℕ in atTop, Stage Γ k O R m (e:=e) J := by
  filter_upwards [OriginalRunMarkedPacketPurchase.selected Γ k O R (e:=e) hG income donor hgrade,
    FundedNativePacketGeometry.insured (e:=e) R hG J] with m hr hgeo
  obtain ⟨Q,hm,levels,ratio,anchor,clock,cl,receipt,crest,cash,sources⟩ := hr
  have sale : Insure v (mass k univ) Q Credit.leanC := by simpa using receipt
  refine ⟨Q,hm,levels,ratio,anchor,clock,cl,sale,crest,?_⟩
  intro N hn a X ha
  obtain ⟨M,laws,observed,_⟩ := sources N hn a X ha
  refine ⟨M,laws,?_⟩
  intro A d F point g room hg hr out n p Y fits P z hz hz1
  have hw (i) : 0<out.outputRadii i/F.kernelCosts i := div_pos (out.output_radius_positive i) (F.kernel_positive i)
  have aperture := hgeo A v (mass k univ) Q hm clock sale
  have size : width k Q hm = VestS v (mass k univ) Q m hm := by
    simp only [OriginalRootedPacketLayout.width, Fintype.card_fin]
  rw [←size] at aperture
  have raw := observed n p Y fits (A.outputNorm m) (fun i=>out.outputRadii i/F.kernelCosts i)
    z (width k Q hm) hw aperture.1 le_rfl aperture.2
  have bill := upper Γ k O R m F a g room hg hr Q hm ha sale cash hz hz1
  exact {raw with roots := fun i=>⟨(raw.roots i).1,(raw.roots i).2.1,(raw.roots i).2.2.trans bill⟩}

end YM.Integration.WilsonLimitConstruction.FundedRunPacketSale
end
