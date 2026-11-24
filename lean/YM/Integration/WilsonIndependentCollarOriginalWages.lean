import YM.Integration.WilsonIndependentCollarProfileBooks
import YM.Integration.WilsonIndependentCollarPhysicalBasis

/-! The two independent chronological wages on the actual funded teacher,
with the physical canonical doses cleared once on each nonempty face. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOriginalWages
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Embroider WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open WilsonIndependentCollarPaidInk WilsonIndependentCollarRootedWidth Pert.Asymptotics
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge}{a:Axis}{simple:G.Simple}{ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G}{R:Run G}{T:Campaign R}{W:Campaign.Pillars R T}

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(k D:Fin n→ℕ)(hk:∀j,k j<D j)(e b h:ℕ):
    let L:=R.family.path.levels
    ∃B:ℝ,1≤B ∧ ∀ᶠfirst:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,
      V.draws=L ∧ V.paid=R.metals.O ∧ V.y=zz L ∧ V.anchor=first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧ Appointed R simple V s D k ∧
      ∀(S:Finset (Fin n))(front:Fin n),front∈S → ∀(A:ℕ),∃C:ℝ,0≤C ∧
      ∀δ:ℝ,0<δ → ∀ᶠm:ℕ in atTop,∀(_hm:V.anchor ≤ m)(days N per:ℕ),m+days≤N → m+1≤N →
      L.S.scale (m+days)-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(i z:ℕ),m ≤ i → i+z ≤ m+days → ∀(hi:V.anchor ≤ i),
      let β:=R.family.path.β N per (m+1)
      let H:=Real.sqrt β
      let rate:=H^δ*B^S.card
      let w:=widths (teacher (prepared s)) (L.clock.J (i+1))
      (∀ (κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)(cell:Digits V.draws (Fin n))
        (q:(j:Fin n)→Choice R k j),
        let Y:=WilsonReceivedCanonicalVerseRegister.start R k κ pt q
        let X:=itinerary V.draws V.paid k N cell z i Y
        Uniform V X i hi rate ∧ Income (V.mint i hi).gear w (e+1) (mass k S) S front X rate) ∧
      ∀v:(j:Fin n)→R.family.label (k j),
        let g:=regulatorRun R.family N per (m+days)
        let size:=L.S.a m/L.S.a (m+days)
        let d:=∑j:S,k j
        ∑q:(j:S)→Choice R k j,(∏j:S,WilsonIndependentCollarOriginalDose.weight R k N per
          (m+days) v j (q j) g size)*rate ≤
            (∏j:S,WilsonIndependentCollarOriginalDose.axisFee R k v j)*C^d*H^((2*A+1)*d)*rate:=by
  intro L
  obtain ⟨B,one,book⟩:=WilsonIndependentCollarProfileBooks.original paid n k D hk e b h
  refine ⟨B,one,?_⟩
  filter_upwards [book] with first data
  obtain ⟨V,draw,chart,year,anchor,cloze,insured,app,earned⟩:=data
  refine ⟨V,draw,chart,year,anchor,cloze,insured,app,?_⟩
  intro S front live A
  obtain ⟨C,paidC,expense⟩:=WilsonIndependentCollarPhysicalBasis.original R simple k A
  refine ⟨C,paidC,?_⟩
  intro δ pos
  filter_upwards [earned S front live A δ (Nat.cast_nonneg _) pos,expense] with m print original
  intro hm days N per top base span i z after before hi β H rate w
  have thermal:L.clock.hatBeta (m+1)/2≤β:=(R.makes.wilson.represents N per (m+1) base).band.1
  have heat:0≤H:=Real.sqrt_nonneg _
  have B0:0≤B:=zero_le_one.trans one
  have rate0:0≤rate:=mul_nonneg (Real.rpow_nonneg heat _) (pow_nonneg B0 _)
  constructor
  · intro κ pt cell q Y X
    obtain ⟨jets,word⟩:=print hm days N β top thermal span i z after before hi κ pt cell q
    refine ⟨fun y J=>shingled_pay (jets y J) (mul_nonneg (Real.rpow_nonneg heat _) B0)
      (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg heat _)),word⟩
    simpa only [pow_one] using pow_le_pow_right₀ one (show 1≤S.card from Finset.card_pos.mpr ⟨front,live⟩)
  · intro v g size d
    rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (original (m+days) N per (by omega) top base span v S) rate0

end YM.Integration.WilsonIndependentCollarOriginalWages
end
