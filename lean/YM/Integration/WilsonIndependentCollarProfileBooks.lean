import YM.Integration.WilsonIndependentCollarCensusCourse
import YM.Integration.WilsonIndependentCollarPointBill

/-! Both the genuine jet tariff and the whole represented group-word wage
hold simultaneously on every subinterval of a moving physical collar. The
canonical source points and derivative directions may vary with the cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarProfileBooks
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonCoeffUV.Embroider
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule WilsonIndependentCollarCensusCourse
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open WilsonIndependentCollarRootedWidth WilsonIndependentCollarPaidInk
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T}

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(k D:Fin n→ℕ)(hk:∀x,k x<D x)(e b h:ℕ):
    let L:=R.family.path.levels
    ∃B:ℝ,1≤B ∧ ∀ᶠ first:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,
      V.draws=L ∧ V.paid=R.metals.O ∧ V.y=zz L ∧ V.anchor=first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧ Appointed R simple V s D k ∧
      ∀(S:Finset (Fin n))(v:Fin n),v∈S → ∀(A δ:ℝ),0≤A → 0<δ →
        ∀ᶠ m:ℕ in atTop,∀(_hm:V.anchor ≤ m)(days N:ℕ)(β:ℝ),
          m+days≤N → L.clock.hatBeta (m+1)/2≤β →
          L.S.scale (m+days)-L.S.scale m≤A*(1+Real.log (L.clock.hatBeta (m+1))) →
          ∀(i z:ℕ),m ≤ i → i+z ≤ m+days → ∀(hi:V.anchor ≤ i),
          let w:=widths (teacher (prepared s)) (L.clock.J (i+1))
          ∀ (κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)(cell:Digits V.draws (Fin n))(q:(j:Fin n)→Choice R k j),
            let Y:=WilsonReceivedCanonicalVerseRegister.start R k κ pt q
            let X:=itinerary V.draws V.paid k N cell z i Y
            Uniform V X i hi ((Real.sqrt β)^δ*B) ∧
            Income (V.mint i hi).gear w (e+1) (mass k S) S v X ((Real.sqrt β)^δ*B^S.card):=by
  intro L
  obtain ⟨B,one,seed⟩:=WilsonIndependentCollarPointBill.original R D k e (w:=1) zero_lt_one
  obtain ⟨P,finance⟩:=WilsonIndependentCollarOpticalTrial.tariff G D k e
  refine ⟨B,one,?_⟩
  filter_upwards [WilsonIndependentCollarCensusCourse.original paid n k D hk e b h] with first data
  obtain ⟨V,draw,chart,clock,anchor,school,sale,dorm,law,fees,appointed⟩:=data
  refine ⟨V,draw,chart,clock,anchor,school,sale,appointed,?_⟩
  intro S v front A δ hA hp
  let F:=WilsonIndependentCollarInkPrice.cost G P (mass k S) (e+1) S.card (Fintype.card (S.erase v))
  obtain ⟨openAt,openAll⟩:=eventually_atTop.mp fees
  filter_upwards [WilsonIndependentCollarOpticalSpan.original R simple (P.prodC F) A hA δ hp,eventually_ge_atTop openAt] with m offer released
  intro hm days N β cut temp span i z after before hi w κ pt cell q Y X
  obtain ⟨Z,room,bill⟩:=offer e V hm draw clock days β temp span
  have small:PadRank V i (i+z) Z:=⟨fun j leJ je=>room.year j (after.trans leJ) (je.trans before),
    (Nat.cast_le.mpr (show i+z-i ≤ m+days-m by omega)).trans room.lengthS⟩
  obtain ⟨good,entry⟩:=seed κ pt q
  have Bp:0≤B:=zero_le_one.trans one
  have ready:Uniform V X i hi (P.buy Z*B):=finance V school dorm N cell Y good i z hi (before.trans cut)
    B Z Bp small entry (fun y J j hj r=>(entry y J j hj r).shave (law (i+z) (by omega)).1)
    (fun j hj _ _=>(law j hj).2.2)
  have year:V.y i≤Z:=room.year i after (by omega)
  have limit:1≤Z:=(V.depth i hi).trans year
  have pp:=P.purchase limit
  have ff:=F.purchase limit
  rw [Credit.products] at bill
  have jet:P.buy Z≤(Real.sqrt β)^δ:=(le_mul_of_one_le_right (zero_le_one.trans pp) ff).trans bill
  have word:F.buy Z≤(Real.sqrt β)^δ:=(le_mul_of_one_le_left (zero_le_one.trans ff) pp).trans bill
  have result:Wellness k X:=sound V.draws V.paid k N cell V.hG V.green Y good z i (before.trans cut)
  obtain ⟨fee,strip,_⟩:=openAll i (released.trans after) hi S
  have price:=WilsonIndependentCollarPaidInk.dated V w i hi k S v front X (fun y=>result.level' y S)
    P B Z Bp limit year ready (law i hi).2.1 (law i hi).1 fee strip
  refine ⟨fun y J=>shingled_pay (ready y J) (mul_nonneg (zero_le_one.trans pp) Bp) (mul_le_mul_of_nonneg_right jet Bp),?_⟩
  intro o j hj r printed family
  obtain ⟨μ,born,salary⟩:=price.2.2 o j hj r
  exact ⟨μ,born,salary.1,salary.2.1,salary.2.2.trans (mul_le_mul_of_nonneg_right word (pow_nonneg Bp _))⟩

end YM.Integration.WilsonIndependentCollarProfileBooks
end
