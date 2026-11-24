import YM.Integration.WilsonIndependentReportedPhysicalTable

/-! A request's stopped density depends on that request's sites on the chosen
course. Signed spatial quadratures can therefore use one common period tariff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentReportedCell
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open WilsonIndependentRawRosterWord WilsonIndependentRawWordGeometry
open scoped Classical ENNReal NNReal

variable {G:Gauge}{I J:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    {M:J → ℕ}{n:Page M → Side}{S:Heir n G}(T:S.Accounts)
    (sites:J → I → Cover)

theorem on_page {M':J → ℕ}{X:Page M' → Type}
    (P Q:∀ w,X (Page.opening M' w))(step:∀ t:Flap M',X t.prev → X t.next)
    (w:J)(same:P w=Q w) (k:ℕ)(bound:k ≤ M' w):
    seriesC P step ⟨w,k,bound⟩=seriesC Q step ⟨w,k,bound⟩:=by
  induction k with
  | zero => exact same
  | succ k ih => exact congrArg (step (⟨w,k,bound⟩:Flap M')) (ih (by omega))

theorem same_stop (other:J → I → Cover)(w:J)(here:sites w=other w):
    (WilsonIndependentRawRosterOrbit.report R W σ d key arms T sites).main (Page.finallyW M w)=
      (WilsonIndependentRawRosterOrbit.report R W σ d key arms T other).main (Page.finallyW M w):=by
  apply on_page
  rw [here]

theorem uniform {Cell:J → Type}[∀w,Fintype (Cell w)][∀w,Nonempty (Cell w)]
    (fee:∀w,Cell w → ℝ)(price:ℝ → ℕ → J → ℝ)
    (issued:∀pick:∀w,Cell w,∃A:ℝ,0 ≤ A ∧ ∃k:ℕ,∀w,fee w (pick w) ≤ price A k w):
    ∃A:ℝ,0 ≤ A ∧ ∃k:ℕ,∀w t,fee w t ≤ price A k w:=by
  classical
  have maximum (w:J):∃s:Cell w,∀t,fee w t ≤ fee w s:=by
    obtain ⟨s,_,h⟩:=Finset.exists_max_image (Finset.univ:Finset (Cell w)) (fee w) Finset.univ_nonempty
    exact ⟨s,fun t=>h t (Finset.mem_univ t)⟩
  choose s hs using maximum
  obtain ⟨A,hA,k,hk⟩:=issued s
  exact ⟨A,hA,k,fun w t=>(hs w t).trans (hk w)⟩

end YM.Integration.WilsonIndependentReportedCell
