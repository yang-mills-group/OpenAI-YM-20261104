import YM.QuadraticLocal.Class.Raffle
import YM.QuadraticLocal.Perspective.Regency
import YM.QuadraticLocal.Mentor.Sealed
import YM.Integration.WilsonMovingMentorSeats
import YM.Integration.WilsonMovingMentorRootRadius

/-! One original set of teaching offices on the selected covariance gives both
the physical course and its stage-uniform bound for the registered input fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorPageTuition
open Precision RG RG.Supply Push Push.PriceCompiler PhysicalNext PhysicalNext.ThroughLaunch Org Next.Foundations
open PhysicalNext.Repeat AllOrder.Floe.Step QuadraticLocal
open WilsonOriginalMovingForestRoots

def Taught {G : Gauge} (simple : G.Simple) (ψ : ℕ → ℕ) : Continuation G := fun _ _ _ pre {M} {D} {A} F =>
  ∀ r : PlanV.Roots (G:=G) M.p.profile M.K M.p.kernel, HEq pre r →
    let Q := WilsonMovingMentorSeats.appointment (M:=M) simple D r
    ∃ (K0 : Mentor.Offices.Books r D Q ψ) (Qa : Mentor.Forecast r D Q ψ K0),
      Mentor.Offices.Sales r D Q F.shape F.scout ψ K0 ∧
        Mentor.Educated r D Q F.shape F.scout ψ K0 A.delay ∧
        (∀ j, Poetry.Agenda.Crews r ψ j (D.L j).val) ∧
        (∀ j, MintClock.Employment r ψ j (D.L j)) ∧
        MintClock.Hospital r D Q F.target ψ K0 Qa A.delay ∧ MintClock.Regency r D Q F.target ψ K0 Qa A.delay ∧
        Spill.Raffle.Warm G r A.delay ψ ∧ WilsonMovingMentorRootRadius.Income (M:=M) r ψ A.delay

theorem entered {G : Gauge} (simple : G.Simple) (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ)
    (ψ : ℕ → ℕ) (shorter : MintClock.splits ≤ ψ) (s : Sheet G) (cost : MapPrices)
    (r : PlanV.Roots (G:=G) s.profile (raging s cost) s.kernel) :
    WilsonMovingCommonPrices.Prepaid ask slow (@Taught G simple ψ _ _ _ r) s (raging s cost) := by
  intro rows E charts C v baton wanting wage
  have rates := WilsonMovingMentorTuition.before ask E wanting wage
  obtain ⟨u,tuition⟩ := Mentor.leases rows
    (fun j i _=> (rates j i).1) (fun j i _=> (rates j i).2.1)
  obtain ⟨h,gather⟩ := Poetry.Agenda.widen r ψ
  obtain ⟨floor,openAt⟩ := MintClock.opens r ψ shorter
  refine ⟨(u ⊔ h) ⊔ floor,?_⟩
  intro l hl earlier D w fees Z φ S θ p P V pocket cap
  obtain ⟨both,hire⟩ := sup_le_iff.mp hl
  obtain ⟨hu,hh⟩ := sup_le_iff.mp both
  let M : Metals G := ⟨raise s l,raging s cost,chart G,chart_ok G⟩
  let Q := WilsonMovingMentorSeats.appointment (M:=M) simple D r
  have crews (j : ℕ) : Poetry.Agenda.Crews r ψ j (D.L j).val :=
    gather j _ ((hh j).trans (D.large j).need)
  have institute : Mentor.Institute (S:=M.p) rows M.p.floorL :=
    fun j i stage L enough=> tuition j i stage L ((hu j).trans enough)
  obtain ⟨books,sales⟩ := Mentor.Offices.formation (X:=M) r D Q Z S ψ crews charts
    pocket (fun j=> (D.large j).need) institute
  obtain ⟨W,hw,study⟩ := Mentor.educates (X:=M) r D Q Z S ψ books sales V
  obtain ⟨Qa⟩ := Mentor.speculate (X:=M) r D Q ψ books
  have active (j : ℕ) : MintClock.Employment r ψ j (D.L j) := openAt j (D.L j) ((hire j).trans (D.large j).need)
  let targets : Targets M.p M.K := rows
  obtain ⟨W₁,h₁,clinic⟩ := MintClock.hospitals (X:=M) r D Q targets ψ books Qa W active
  obtain ⟨W₂,h₂,income⟩ := MintClock.regents (X:=M) r D Q targets ψ books Qa W₁ active
  obtain ⟨W₃,h₃,insured⟩ := Spill.Raffle.accrues (X:=M) G r W₂ ψ
  obtain ⟨W₄,h₄,radius⟩ := WilsonMovingMentorRootRadius.accrued (M:=M) r ψ W₃
  refine ⟨W₄,hw.trans (h₁.trans (h₂.trans (h₃.trans h₄))),?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides r' equal
  have stage := h₄.trans hW
  have same : r = r' := eq_of_heq equal
  subst r'
  exact ⟨books,Qa,sales,study _ (h₁.trans (h₂.trans (h₃.trans stage))),crews,active,
    clinic _ (h₂.trans (h₃.trans stage)),income _ (h₃.trans stage),insured _ stage,radius _ hW⟩

end YM.Integration.WilsonMovingMentorPageTuition
end
