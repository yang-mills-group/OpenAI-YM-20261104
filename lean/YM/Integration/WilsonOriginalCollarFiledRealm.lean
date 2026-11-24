import YM.Integration.WilsonOriginalCollarTeacher
import YM.Integration.WilsonOriginalCompoundVertexStrip

/-! Read all marked rows, old action and freshly issued compilers on one actual mint. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCollarFiledRealm
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher
open scoped Classical BigOperators
variable {G : Gauge}

/-- Numerical receipts at the current physical stage. Both adjacent
teacher stages may issue the same print. The actual group word enters later. -/
def Filed (request : Request G) (R : Run G) : Prop := ∀ (n : ℕ) (k D : Fin n → ℕ)
    (hk : ∀ a, k a < D a) (e b h : ℕ), ∀ᶠ first : ℕ in atTop,
    ∃ V : Realm G (e+1) Credit.leanC, V.draws = R.family.path.levels ∧ V.paid = R.metals.O ∧
      V.y = zz R.family.path.levels ∧ V.anchor = first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧
      Nonempty (Tribe V (hol G) Credit.leanC Credit.leanC (counter (hol G) (primes G) k D hk)) ∧
      ∀ m, ∀ hm : V.anchor ≤ m, let A := R.family.path.levels
        let j := A.clock.J (m+1)
        let z := Borough.ageZ (A.clock.hatBeta m)
        let U := V.mint m hm
        ∃ live : 5 ≤ j, U.σ = crestM A m live ∧ nimbus U.gear ≤ z ∧
          (∀ a (ha : a ≤ e+1) k r, WilsonOriginalCompoundVertex.Income R m a k r U.σ
            ((WilsonOriginalCompoundVertex.tariff G e a k r ha).buy z)) ∧
          ∀ p k, p ≤ j → k ≤ j →
            let s := widths request j
            let out := WilsonIndependentCollarPrintIncome.issue s p k U.gear
            out.fee ≤ z ∧ out.strip⁻¹ ≤ z ∧
            (p = e → out.strip ≤ (holt V m hm (s.requested p k U.gear) (s.admitted p k U.gear)).s) ∧
            (∀ t H, t ≤ j+1 → H ≤ j+1 → WilsonIndependentCollarPrintIncome.strip s p k U.gear ≤
              WilsonThermometerUnitFilingWeakStrip.trial request R.metals.p.kernel t H) ∧
            (∀ x, x = A.clock.J m ∨ x = j → teacherWidth request R.metals.p.kernel x ≤ out.strip)

theorem original (R : Run G) (simple : G.Simple) (request : Request G)
    (paid : FundedMarkedCoverRows.prices (prices request) R.kit) : Filed request R := by
  intro n k D hk e b h
  filter_upwards [WilsonOriginalCollarMint.realm R simple (prices request) paid n k D hk e b h]
    with first invoice
  obtain ⟨V,levels,chart,clock,anchor,declared,covered,school,dates⟩ := invoice
  refine ⟨V,levels,chart,clock,anchor,declared,covered,school,?_⟩
  intro m hm A j z U
  obtain ⟨live,stamp,shape,past,wage⟩ := dates m (anchor ▸ hm) hm
  have kernel : U.gear.kernel = A.clock.kernel := by change V.draws.clock.kernel = _; rw [levels]
  have genuine : A.clock.kernel = R.metals.p.kernel := R.alloy.B.valid.kernel
  have cost : prices request j U.gear ≤ z := by
    simpa only [A,j,z,U,Realm.cash,Credit.lean_cost,clock,zz,Borough.ageZ] using wage
  refine ⟨live,stamp,(le_max_left ..).trans cost,?_,?_⟩
  · intro a ha k r N M date lifted θ
    obtain ⟨action,limit,trunk,shelf⟩ :=
      ((Fk.export_domain G Credit.leanC (e+1) a k r ha).choose_spec.money V m hm).2 N M date lifted
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using action
    · simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using limit
    · simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using trunk
    intro pastDate
    have cell := shelf pastDate
    simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ]
      using And.intro cell.1 cell.2.1
  · intro p k hp hk s out
    have charge := charged request j p k U.gear hp hk cost
    refine ⟨charge.2.1,charge.2.2,?_,?_,?_⟩
    · rintro rfl; exact out.narrow
    · intro t H ht hH
      have less : WilsonIndependentCollarPrintIncome.strip s p k U.gear ≤ common request U.gear.kernel j /32 :=
        min_le_left ..
      exact (less.trans (div_le_self (positive ..).le (by norm_num))).trans
        (by rw [kernel,genuine]; exact paid_neutral request _ ht hH)
    · intro x hx
      have inc : A.clock.J (m+1) ≤ A.clock.J m + 1 := A.fits.stepSlow m
      have next : A.clock.J (m+2) ≤ A.clock.J (m+1) + 1 := A.fits.stepSlow (m+1)
      have mono : A.clock.J m ≤ A.clock.J (m+1) := A.fits.mono (Nat.le_succ m)
      rw [← genuine]
      rcases hx with rfl | rfl <;>
        apply at_mint request A m p k _ kernel live shape past <;> dsimp only [j] at * <;> omega

end YM.Integration.WilsonOriginalCollarFiledRealm
end
