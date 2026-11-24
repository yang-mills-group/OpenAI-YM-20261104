import YM.Integration.WilsonOriginalMicroscopicGuardedPosterior
import YM.Integration.WilsonOriginalFailedHaloPosterior

/-! The complete canonical three-field guard change on the true normalized
posterior conditioned on the actual earlier configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedHeld
open Filter Finset MeasureTheory Lattice Wilson RG Source Labels OPE.Therm
open PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicGuardedTrial
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p K i:ℕ}
variable (live:K≤N)(earlier:i+1≤K)(o:Fin 3→Site (R.family.side K p))
    (v:∀a:Fin 3,R.family.label (d a))(s:Finset (Fin 3))
local notation "Y" => gap R d N p K o v s
local notation "μ" W:max => WilsonMacroscopicRichFlatPosteriorLaw.law R N p earlier W
local notation "E" => SelectedCofactorAnchoredRegister.hot (G:=G)
  (R.family.path.rep N p K).p.threshold (footprint R d p K o s)
local notation "M" => WilsonOriginalMicroscopicGuardedPosterior.gross R d N p K v s

include live in
theorem original (W:Config G (R.family.side i p)):
    actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans earlier) W=(∫U,Y U ∂(μ W)) ∧
    ‖actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans earlier) W‖
      ≤ M*(μ W).real E:=by
  obtain ⟨borel,gross,clear,_⟩:=occupied R d N p K o v s
  letI:IsProbabilityMeasure (scene R.family.path N p K):=probability R.makes.wilson live
  letI:IsProbabilityMeasure (μ W):=WilsonMacroscopicRichFlatPosteriorLaw.prob R earlier live W
  have invoice:Integrable Y (scene R.family.path N p K):=
    Integrable.of_bound borel.aestronglyMeasurable M (ae_of_all _ gross)
  have read:actualTransport R.family (N:=N) Y ((Nat.le_succ i).trans earlier) W=∫U,Y U ∂(μ W):=by
    calc
      _=WilsonMacroscopicForwardTransfer.exterior (C:=R.family) (N:=N) ((Nat.le_succ i).trans earlier) Y W:=
        congrFun (WilsonSeparatedOriginalPosteriorTransport.realized (C:=R.family) (N:=N) (p:=p)
          R.makes live ((Nat.le_succ i).trans earlier) Y invoice).symm W
      _=_:=WilsonMacroscopicRichFlatPosteriorLaw.reading R earlier live W Y invoice
  refine ⟨read,?_⟩
  rw [read]
  have mp:0≤M:=(norm_nonneg (Y 1)).trans (gross 1)
  have due:=WilsonOriginalFailedHaloPosterior.envelope (μ W) ({()}:Finset Unit)
    (fun _=>E) (fun _ _=>SelectedCofactorAnchoredRegister.measurable _ _) (fun _=>(μ W).real E)
    (fun _ _=>le_rfl) Y borel (le_refl 0) mp gross
    (fun U allowed=>by rw [clear U (allowed () (by simp))];simp)
  simpa using due

end YM.Integration.WilsonOriginalMicroscopicGuardedHeld
end
