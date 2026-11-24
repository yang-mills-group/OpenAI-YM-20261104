import YM.Integration.WilsonOriginalAllOrderAcceptance
import YM.Integration.WilsonOriginalAllOrderChamber

/-! A requested discrete event and compiled word on every later mint of
one original realization, after fixing the public run. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalAllOrderActualMint
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar
open scoped Classical BigOperators
open WilsonOriginalAllOrderCalendar WilsonOriginalAllOrderCourse
variable {G : Gauge} {a : Axis} {simple : G.Simple} {ε : ℝ}
variable {s : WilsonOriginalAllOrderCourse.Schedule G} {R : Run G} {T : Campaign R}
variable {W : Campaign.Pillars R T}

theorem original (paid : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε s R T W) (key : Key)
    (n : ℕ) (k D : Fin n → ℕ) (hk : ∀ j, k j < D j) (e b h rank : ℕ) :
    ∀ᶠ first : ℕ in atTop, ∃ V : Realm G (e+1) Credit.leanC, V.draws = R.family.path.levels ∧
      V.paid = R.metals.O ∧ V.y = zz R.family.path.levels ∧ V.anchor = first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧
      Nonempty (Tribe V (hol G) Credit.leanC Credit.leanC (counter (hol G) (primes G) k D hk)) ∧
      ∀ m, ∀ hm : V.anchor ≤ m,
        let A := R.family.path.levels
        let j := A.clock.J (m+1)
        let z := Borough.ageZ (A.clock.hatBeta m)
        let U := V.mint m hm
        let w := widths (teacher s) j
        let out := WilsonIndependentCollarPrintIncome.issue w e rank U.gear
        ∃ live : 5 ≤ j, U.σ = crestM A m live ∧
          (s.fixedDigit key j).price U.gear ≤ z ∧ out.fee ≤ z ∧ out.strip⁻¹ ≤ z ∧
          out.strip ≤ (holt V m hm (w.requested e rank U.gear) (w.admitted e rank U.gear)).s ∧
          (∀ x, x = A.clock.J m ∨ x = j → teacherWidth (teacher s) R.metals.p.kernel x ≤ out.strip) ∧
          (∀ z₀ (hz : z₀ ≤ e+1) k r, WilsonOriginalCompoundVertex.Income R m z₀ k r U.σ
            ((WilsonOriginalCompoundVertex.tariff G e z₀ k r hz).buy z)) := by
  let gate := max (Encodable.encode key) (max e rank)
  obtain ⟨start,openAfter⟩ := eventually_atTop.mp (R.family.path.levels.fits.deep.eventually_ge_atTop gate)
  filter_upwards [paid.mint n k D hk e b h,eventually_ge_atTop start] with first mint ready
  obtain ⟨V,path,bank,clock,anchor,strip,insure,people,dates⟩ := mint
  refine ⟨V,path,bank,clock,anchor,strip,insure,people,?_⟩
  intro m hm A j z U w out
  have visit : gate ≤ j := openAfter (m+1) (ready.trans ((anchor ▸ hm).trans (Nat.le_succ _)))
  obtain ⟨live,stamp,_,eventsPaid,positive,words⟩ := dates m hm
  have event := eventsPaid (Encodable.encode key) ((le_max_left ..).trans visit)
  obtain ⟨fare,breadth,seat,_,teacherPaid⟩ := words e rank
    (((le_max_left ..).trans (le_max_right ..)).trans visit)
    (((le_max_right ..).trans (le_max_right ..)).trans visit)
  exact ⟨live,stamp,by simpa only [events,indexed] using event,fare,breadth,seat rfl,teacherPaid,positive⟩

end YM.Integration.WilsonOriginalAllOrderActualMint
end
