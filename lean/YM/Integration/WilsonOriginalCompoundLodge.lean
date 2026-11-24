import YM.Integration.WilsonOriginalCompoundStrip
import YM.Integration.WilsonThermometerUnitFilingWeakRoom
import YM.Integration.WilsonEmittedDictionaryForecast

/-! The finite roster of actual auxiliary gauge forests is known after the
block side has been bought. Enrol the separately chosen conditional fees then. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalCompoundLodge
open Function Filter Finset Lattice Laurent Wilson RG RG.Shoot RG.Supply Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Input Org Next.Foundations Push.PriceCompiler
open FormalBulk08 Flat Work.F08 Next.Free Stationary
open WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonThermometerUnitFilingWeakRoom
open scoped Classical BigOperators
variable {G:Gauge}

private theorem ext_flag {X:Patch}{F F':Lodge X}(same:F.aim=F'.aim):F=F':=by
  cases F
  cases F'
  congr

private instance (X:Patch):Finite (Lodge X):=Finite.of_injective (fun F:Lodge X=>F.aim) (fun _ _ h=>ext_flag h)
private noncomputable instance (X:Patch):Fintype (Lodge X):=Fintype.ofFinite _

private def cash (G:Gauge)(K:KernelChoices)(X:Patch)(t:ℕ)(ht:4 ≤ t)(F:Lodge X):ℝ:=
  ((book G K X.J t).serves X.order_cut ht |>.conditional X rfl F).choose

private def schedule (G:Gauge):Cost:=fun X K _ t=>
  if ht:4 ≤ t then ∑F:Lodge X,cash G K X t ht F else 0

def Filed : Prediction G:=@WilsonEmittedDictionaryForecast.Filed G (schedule G)

theorem original (Q:WilsonOriginalCompoundStrip.Request G)(cap U:ℕ→ℕ)(mono:Monotone cap)(simple:G.Simple){ε:ℝ}(pos:0<ε):
    WilsonOriginalCourseSupplement.Award
      (WilsonWindowJointPurchase.Together (@WilsonOriginalCompoundStrip.Filed G Q) (@Filed G))
      (WilsonEmittedPositionSchool.funded.{u} cap U mono simple pos):=by
  apply WilsonEmittedPositionSchool.withSupplement _ _ cap U mono simple pos
  intro s price
  exact WilsonWindowJointPurchase.joint
    (WilsonOriginalProfileStrip.prepaid (WilsonOriginalCompoundStrip.programme Q) simple s _)
    (WilsonEmittedDictionaryForecast.prepaid (schedule G) s _)

theorem figure (R:Run G)(fund:Filed R.kit)(i:ℕ)(ht:4 ≤ R.alloy.B.a.clock.J i):
    let A:=R.alloy.B.a
    let K:=R.metals.p.kernel
    let X:Patch:=(A.clock.op i 0).patch
    let σ:=(book G K X.J (A.clock.J i)).width
    ∀F:Lodge X,∃c:ℝ,0<c ∧ c ≤ Borough.ageZ (A.clock.hatBeta i) ∧
      ∀N M:ℕ,i<N → N ≤ M → ∀ hh:X.Branches K G,
        let z:=destination A N i
        (Flat.gamma G K z F hh).strip σ c ∧ (Flat.locating G K z F).strip σ c ∧
          (Flat.roots G K z F).strip σ c:=by
  intro A K X σ F
  let t:=A.clock.J i
  have held:=((book G K X.J t).serves X.order_cut ht).conditional X rfl
  have cash_pos (F':Lodge X):0<cash G K X t ht F':=(held F').choose_spec.1
  have each (F':Lodge X):cash G K X t ht F' ≤ ∑L:Lodge X,cash G K X t ht L:=
    Finset.single_le_sum (fun l _=>(cash_pos l).le) (Finset.mem_univ F')
  have hX:X.J=A.clock.J (i+1):=rfl
  have paid:=fund i X rfl hX t (hX.symm ▸ A.fits.mono (Nat.le_succ i))
  change |schedule G X K (R.metals.p.profile X.J) t| ≤ Borough.ageZ (A.clock.hatBeta i) at paid
  have quote:schedule G X K (R.metals.p.profile X.J) t=∑L:Lodge X,cash G K X t ht L:=by
    unfold schedule
    split <;> rename_i decision
    · rfl
    · exact False.elim (decision ht)
  rw [quote] at paid
  refine ⟨cash G K X t ht F,cash_pos F,(each F).trans ((le_abs_self _).trans paid),?_⟩
  intro N M before later hh
  exact (held F).choose_spec.2 A i N M before later rfl rfl hh

end YM.Integration.WilsonOriginalCompoundLodge
end
