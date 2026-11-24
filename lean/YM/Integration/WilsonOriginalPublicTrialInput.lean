import YM.Integration.WilsonOriginalMicroscopicGuardedPageSchool
import YM.Integration.WilsonPositionProgramMeteredPublicResponse

/-! At a fixed true trial stop, the inverse is chosen once, before phases,
sites, angular grades or forests. Its literal uncut group word and its public
normalized dose use the same numbers, including the unit coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialInput
open Filter Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals Next.Foundations
open WilsonOriginalNullCorridor WilsonOriginalNullPlacedGermMap
open WilsonPositionProgramBlockedPublicExperiment WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalMicroscopicGuardedTrial
open WilsonPositionProgramSubmittedCoordinates (plain submitted)
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))
local notation "F" v:max => R.family.labels.level (d v)

def salary (a:Fin 3):ℝ:=
  stretch R η (j a) K*((1+WilsonOriginalMicroscopicGuardedPage.wrapCost R (d a) (j a))*M a)

def chosen (before:∀a,j a≤K)(registered:Indexed R d j target η M Y)(N per:ℕ):
    (a:Fin 3)→(R.family.label (d a) ≃ₗ[ℂ] R.family.label (d a)) :=
  if live:K<N then (registered K before N per live.le (fun a=>(before a).trans_lt live)).choose
  else fun _=>LinearEquiv.refl _ _

def fitted (before:∀a,j a≤K)(registered:Indexed R d j target η M Y)(N per:ℕ)(a:Fin 3):R.family.label (d a):=
  (chosen R d j K target η M Y before registered N per a).symm (euler R d j Y N per a)

def vector (before:∀a,j a≤K)(registered:Indexed R d j target η M Y)(N per:ℕ)(a:Fin 3):R.family.label (d a):=
  if K<N then WilsonPositionProgramReportedField.entire R (d a) K (N,per)
    (fitted R d j K target η M Y before registered N per a) else 0

def bill (e:ℕ)(phase:Fin 3→ℂ →L[ℝ] ℝ)(a:Fin 3):ℝ:=
  Fintype.card (Alma (F a))*(e+1:ℕ)*(‖phase a‖*
    ((2:ℝ)^(Finset.univ.sup fun v:(F a).Index=>((F a).grades v).2)*
      (salary R d j K η M a)))

theorem original (before:∀a,j a≤K)(registered:Indexed R d j target η M Y)(N per:ℕ)(live:K<N):
    let v:=fitted R d j K target η M Y before registered N per
    let v₀:=vector R d j K target η M Y before registered N per
    let price:=salary R d j K η M
    (∀a, (chosen R d j K target η M Y before registered N per a) (v a)=euler R d j Y N per a ∧
      (F a).coeffSize (v a) ≤ price a) ∧
    (∀(o:Fin 3→Site (R.family.side K per)) (a:Fin 3) U,
      raw R d N per K o v a U =
        ∑l,v₀ a l*WilsonPositionProgramBlockedTrialFiling.atomAt R (d a) N per K (o a) l U) ∧
    (∀(o:Fin 3→Site (R.family.side K per))(s:Finset (Fin 3)) u (age:u≤K),
      (∫U,‖actualTransport R.family (N:=N) (gap R d N per K o v s) age U‖ ∂scene R.family.path N per u) ≤
        WilsonOriginalMicroscopicGuardedWallet.invoice R d K price s*R.family.path.levels.clock.forcedAllowance K) ∧
    ∀{a:ℕ}(child:Fin (a+1)→Fin 3)(dd:Fin (a+1)→ℕ)(fit:∀s,d (child s)<dd s)
      (phase:Fin 3→ℂ →L[ℝ] ℝ)(e:ℕ)(s:Fin (a+1)),
      let X:=submitted R (d ∘ child) dd fit (fun i=>v₀ (child i)) (phase ∘ child)
      (∀l:(F (child s)).Index,X s (plain (F (child s)) l)=PowerSeries.C (phase (child s) (v₀ (child s) l))) ∧
      WilsonPositionProgramNormalizedMaster.fee X e s ≤ bill R d j K η M e phase (child s) :=by
  intro v v₀ price
  let bank:=registered K before N per live.le (fun a=>(before a).trans_lt live)
  have share:=bank.choose_spec
  have fix (a:Fin 3):v a=(bank.choose a).symm (euler R d j Y N per a):=by simp only [v,fitted,chosen,dif_pos live]
  have supplied(a:Fin 3):v₀ a=WilsonPositionProgramReportedField.entire R (d a) K (N,per) (v a):=by
    simp only [v₀,vector,if_pos live,v]
  have cost(a:Fin 3):(F a).coeffSize (v a)≤price a:=by
    rw [fix];exact (share.2.1 a).2.1
  refine ⟨fun a=>⟨LinearEquiv.apply_symm_apply _ _,cost a⟩,?_,?_,?_⟩
  · intro o a U
    simp_rw [supplied]
    exact (WilsonOriginalMicroscopicGuardedTrial.source R d N per K o v live.le a U).2
  · intro o s u age
    rw [funext fix]
    exact share.2.2 o s u age
  · intro a child dd fit phase e s X
    refine ⟨fun l=>WilsonPositionProgramSubmittedCoordinates.entry R _ dd fit _ _ s l,?_⟩
    apply (WilsonPositionProgramSubmittedCoordinates.paid R _ dd fit _ _ e s).trans
    unfold bill
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [supplied]
    exact (WilsonPositionProgramReportedField.purchased R _ K (N,per) live.le _).trans
      (mul_le_mul_of_nonneg_left (cost _) (by positivity))

end YM.Integration.WilsonOriginalPublicTrialInput
end
