import YM.Integration.WilsonThermometerUnitFilingCoverAtom
import YM.RegulatorIR.Profiles.Trek

/-! Finite subsets of the submitted one-name pupil enter the original independent report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverStock
open Function Gauge Lattice RG Wilson QuadraticLocal Marker QuadraticLocal.Earn RegulatorIR
open RegulatorIR.Taping RegulatorIR.Halo RegulatorIR.Profiles RegulatorIR.Prim RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open PertExtension.Series WilsonThermometerUnitFilingCoverAtom Finset
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {o:Passport n Unit} {J:Census Unit} {I X:Type}
  (M:I→Row o J G X) (s:Finset I) (fill:I→ℝ) (site:Cover) {h:ℕ}

def portrait:Portrait G:=∑ i∈s,WilsonThermometerUnitFilingCoverAtom.portrait (M i) site (fill i)

theorem original (grades:∀ i∈s,h≤(M i).lamp.toll+1): LocalStamp (portrait M s fill site) h:=
  stamps s _ fun i hi=>stamped (M i) site (fill i) (grades i hi)

theorem copied {n':Side}(g:ℝ)(U:Config G n')(y:Site n'):
    portrait M s fill 0 g (expandAt y U)=
      ∑ i∈s,fill i * QuadraticLocal.Sunrise.Loan.letter (M i).lamp (M i).atom y g U:=by
  simp only [portrait,Finset.sum_apply,WilsonThermometerUnitFilingCoverAtom.copied]

variable {W:Type} {H:W→ℕ} {sizes:Page H→Side} {S:Heir sizes G} (A:S.Accounts)
  (B:W→Portrait G) (locality:∀ w,LocalStamp (B w) h)

def symbol (w:W):RegulatorIR.Diagram.Orders (Foot G):=(stamp_symbol (locality w)).choose

def report:A.Report h:=declaring A (symbol B locality) fun w=>
  (stamp_symbol (locality w)).choose_spec.2

theorem opening (w:W):
    BasisT h h (B w) ((report A B locality).main (Page.opening H w)) ∧
    (report A B locality).main (Page.opening H w)=symbol B locality w:=by
  have eh:(report A B locality).main (Page.opening H w)=symbol B locality w:=rfl
  exact ⟨eh.symm ▸ (stamp_symbol (locality w)).choose_spec.1,eh⟩

end YM.Integration.WilsonThermometerUnitFilingCoverStock
