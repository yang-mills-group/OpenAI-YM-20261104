import YM.Integration.QLocalInheritedCoverPurchase
import YM.Integration.QLocalInheritedNativeStage

/-! A post-length price whose constants and predicate depend on the original
    selected lattice patch, kernel and both stage numbers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalPatchGate
open Filter Function Lattice Wilson Pressure RG Precision
open Push.PriceCompiler Supply Testing Next.Scheduling
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad Heir Heir.Suite
open ConnectedActivityE6 WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical

variable {G : Gauge}
abbrev Condition (G : Gauge) := ℕ → ℕ → (H : Patch) → (K : KernelChoices) → H.Branches K G → ℝ → Prop

def Paid (cond : Condition G) : Prediction G := fun {M} {D} {A} _ =>
  ∀ j x, A.delay.betaEntry j≤x → ∀ i (step : StepStages j i) (fr : M.p.first ≤ i),
    cond j i (Clockwork.patch D step fr) (query M.p M.K j i).bind (M.p.has _) (betaF G x (D.L j))

theorem prepaid (cond : Condition G)
    (finite : ∀ j i H K h, ∀ᶠ z : ℝ in atTop, cond j i H K h z)
    (s : Sheet G) (K : MapPrices) : Prepaid (Paid cond) s K := by
  intro Q E hc C fee b hw
  refine ⟨fun _ => 0, fun _ _ D _ _ _ _ _ _ _ _ V _ => ?_⟩
  have stage j i : ∀ᶠ x : ℝ in atTop, ∀ (step : StepStages j i) (fr : s.first ≤ i),
      cond j i (Clockwork.patch D step fr) (query s K j i).bind (s.has _) (betaF G x (D.L j)) := by
    by_cases h : (StepStages j i ∧ s.first ≤ i)
    · have timed := (Work.E09.betaF_growth G (D.L j)).eventually
        (finite j i (Clockwork.patch D h.1 h.2) (query s K j i).bind (s.has _))
      exact timed.mono fun _ hx _ _ => hx
    exact Eventually.of_forall fun _ st hi => (h ⟨st,hi⟩).elim
  obtain ⟨β,_,hβ,h⟩ := collect_upper V.betaEntry _
    (fun j => eventually_transitions j _ _ (fun i _ => stage j i))
  refine ⟨{V with betaEntry:=β},⟨hβ,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW B I hp B' A η q E' X J K' b' hZ hY hm
  exact fun j x hx i st fr => h j x ((hW.beta j).trans hx) i st st fr

theorem selected (R : Run G) (cond : Condition G) (paid : Paid cond R.kit)
    {N m : ℕ} (period : ℕ) (hm : m<N) :
    let a := R.alloy.B.a
    let S := a.clock.op m period
    ∀ h : S.patch.Branches S.kernel G,
      cond (a.clock.J (m+1)) (a.clock.J m) S.patch S.kernel h (a.clock.hatBeta (m+1)) := by
  intro a S h
  let j := a.clock.J (m+1)
  let i := a.clock.J m
  have st := step_paid a m
  have fr := first_le R.alloy.B.valid m
  have hv := Testing.proceeds R.alloy.B N m period hm
  have hL : S.patch.L=R.rolls.L j := block_eq R.alloy.B.valid m
  have hJ : S.patch.J=j := hv.atStep
  have hP : S.patch=Clockwork.patch R.rolls st fr := by
    cases hh : S.patch
    rw [hh] at hL hJ
    unfold Clockwork.patch
    congr
  have hβ := Application.clock_next a m period
  change a.clock.hatBeta (m+1)=betaF G (a.clock.hatBeta m) S.patch.L at hβ
  have hK : S.kernel=(query R.metals.p R.metals.K j i).bind := hv.knobs
  have hb : a.clock.hatBeta (m+1)=betaF G (a.clock.hatBeta m) (R.rolls.L j) :=
    hβ.trans (congrArg (betaF G (a.clock.hatBeta m)) hL)
  have carry {D D' : Patch} {K K' : KernelChoices} {x x' : ℝ}
      (hD : D=D') (hK : K=K') (hx : x=x') {s : D.Branches K G} {s' : D'.Branches K' G}
      (u : cond j i D K s x) : cond j i D' K' s' x' := by
    subst D'; subst K'; subst x'; exact u
  exact carry hP.symm hK.symm hb.symm (paid j _ (R.alloy.B.valid.pays m) i st fr)

end YM.Integration.QLocalPhysicalPatchGate
end
