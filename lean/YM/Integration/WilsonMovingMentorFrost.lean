import YM.Integration.WilsonMovingMentorSchools
import YM.Integration.WilsonMovingMentorOffer

/-! The analytic bounds for the original physical representatives on the full
finite cutoff course, charged at the same register and delay as the old fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorFrost
open RG Push PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Org RG.Supply Push.PriceCompiler ThroughLaunch
open WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor

def Held {G : Gauge} : Prediction G := fun {_} {_} {A} F => QuadraticLocal.Beaming.Frost F.shape F.book F.scout A.delay

theorem paid {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Held G)) := by
  intro s T rows E charts C v baton wanting wage
  have rates := WilsonMovingMentorTuition.before ask E wanting wage
  obtain ⟨u,visits⟩ := QuadraticLocal.Beaming.orbit rows
    (fun j i _ => (rates j i).1) (fun j i _ => (rates j i).2.1)
  refine ⟨u,?_⟩
  intro l hl earlier D w fees Z φ S θ p P V pocket cap
  let M : Metals G := ⟨raise s l,raging s T,chart G,chart_ok G⟩
  obtain ⟨W,hw,accepted⟩ := QuadraticLocal.Beaming.option Z φ S pocket
    (show QuadraticLocal.Beaming.Freq (P':=M.p) rows u from visits)
    (fun j => (hl j).trans (D.large j).need) V
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owner menu
  exact accepted _ hW

theorem actual {G : Gauge} (R : Run G) (held : Held R.kit) (m : ℕ) :
    QuadraticLocal.Beaming.Celebrates R.kit.shape R.kit.book R.kit.scout
      (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) (R.alloy.B.a.clock.hatBeta m) :=
  held.bears _ _ _ (step_paid R.alloy.B.a m) (R.alloy.B.valid.pays m)

end YM.Integration.WilsonMovingMentorFrost
end
