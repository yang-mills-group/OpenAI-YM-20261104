import YM.Integration.WilsonEmittedDictionary
import YM.Integration.WilsonNeutralPointForecast

/-! The original before-course menu pays the compact group-field dictionary on every physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedDictionaryForecast
open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Next.Foundations Push.PriceCompiler
open FormalBulk08 WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedDictionaryPatchPrices
open scoped Classical BigOperators
variable {G:Gauge}

def Enrolled (C:Cost) (K:KernelChoices) (f:ℕ→Stage) (A:Levels G) : Prop :=
  ∀ i,∀ X:Patch,X.L=A.S.block i → X.J=A.clock.J (i+1) →
    ∀ k≤X.J, |C X K (f X.J) k| ≤ Borough.ageZ (A.clock.hatBeta i)

def Filed (C:Cost) : Prediction G := fun {M} {_} {A} _ => Enrolled C M.p.kernel M.p.profile A.B.a

private theorem patch_same {X Y:Patch} (l:X.L=Y.L) (j:X.J=Y.J) : X=Y:=by
  cases X
  cases Y
  cases l
  cases j
  rfl

theorem prepaid (C:Cost) (s:Sheet G) (price:MapPrices) :
    WilsonFundedWindowMenu.Prepared (Filed (G:=G) C) s price := by
  intro targets fees flags programs wages baton
  refine ⟨0,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  let table:=WilsonLimitConstruction.FundedDictionaryPatchPrices.post C s (fun j=>(D.L j).val)
  let q (j:ℕ)(x:ℝ):Prop:=∀ k≤j, |table k j| ≤ Borough.ageZ x
  obtain ⟨raised,other,_,pay⟩:=delay_extra V q (fun _ _ _=>True) (fun j=>by
    filter_upwards [Borough.age_fly.eventually (eventually_ge_atTop (∑k∈range (j+1),|table k j|))] with x ripe
    exact fun k hk=>(single_le_sum (f:=fun k=>|table k j|) (fun n _=>abs_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le hk))).trans ripe)
    (fun _ _=>Filter.Eventually.of_forall fun _=>trivial)
  refine ⟨raised,other,?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q₀ exchange aux rider booth sheltered works divides i X side stage k admit
  have left:X.L=D.L (B.a.clock.J (i+1)):=by
    rw [side,←B.a.fits.sameFactor i,B.valid.lengths]
  let j:=B.a.clock.J (i+1)
  have found:∃ X:Patch,X.L.val=(D.L j).val ∧ X.J=j:=⟨X,congrArg Subtype.val left,stage⟩
  have same:(Classical.choose found)=X:=by
    have side':(Classical.choose found).L=X.L:=Subtype.ext ((Classical.choose_spec found).1.trans (congrArg Subtype.val left).symm)
    have stage':(Classical.choose found).J=X.J:=(Classical.choose_spec found).2.trans stage.symm
    exact patch_same side' stage'
  have read:table k j=C X s.kernel (s.profile j) k:=by
    dsimp only [table,WilsonLimitConstruction.FundedDictionaryPatchPrices.post]; rw [dif_pos found,same]
  change |C X s.kernel (s.profile X.J) k|≤_
  rw [stage,←read]
  exact (pay Y hY).1 _ _ (B.valid.pays i) k (stage ▸ admit)

theorem original (C:Cost)(R:Run G)(h:G.Simple)(bill:Filed C R.kit) : Covered C R := by
  intro k
  let A:=R.family.path.levels
  have deep:Tendsto (fun i:ℕ=>A.clock.J (i+1)) atTop atTop:=A.fits.deep.comp (tendsto_add_atTop_nat 1)
  have grows:Tendsto (fun i=>Real.log (Real.log (A.clock.hatBeta i))) atTop atTop:=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (WardBin.bell A h))
  filter_upwards [deep.eventually_ge_atTop k,grows.eventually_ge_atTop 1] with i hi large
  intro per
  let X:=(A.clock.op i per).patch
  have node:X.J=A.clock.J (i+1):=(Pressure.Testing.proceeds R.alloy.B (i+1) i per (Nat.lt_succ_self i)).atStep
  have kernel:A.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
  have stage:A.params (i+1)=R.metals.p.profile X.J:=by
    rw [node]; exact Push.PriceCompiler.params_eq R.alloy.B.valid _
  have paid:|selected C R i per k| ≤ 1+Real.log (Real.log (A.clock.hatBeta i)):=by
    change |C X A.clock.kernel (A.params (i+1)) k|≤_
    rw [kernel,stage]
    exact bill i X rfl node k (node ▸ hi)
  refine ⟨paid,?_⟩
  intro U J T
  let x:=Real.log (Real.log (A.clock.hatBeta i))
  have grown:1+x ≤ A.clock.monitor i:=by
    change 1+x≤Real.exp (x^2)
    have hx:1≤x:=large
    have hs:x≤x^2:=by nlinarith only [mul_nonneg (sub_nonneg.mpr hx) (zero_le_one.trans hx)]
    linarith [Real.add_one_le_exp (x^2)]
  exact paid.trans (grown.trans ((le_add_of_nonneg_right (Real.exp_pos _).le).trans (T.monitor_cost i)))

end YM.Integration.WilsonEmittedDictionaryForecast
end
