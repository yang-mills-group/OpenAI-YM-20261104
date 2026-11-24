import YM.Integration.WilsonReportingMeasuredWardIntakePrice

/-! Actual all-cutoff budget of the unmasked source on the earlier Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardFunding
open Filter Finset Lattice RG Wilson Source MS.Local.Physical MS.Theater MS.Land
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldWardWallet
open WilsonReportingMeasuredWardSourceGerm WilsonReportingMeasuredWardIntake
open scoped Classical BigOperators

variable {G:Gauge} {R:Run G} {B:Deck G} {T:Campaign R} (W:Campaign.Pillars R T) (Q:Prescription B)
local notation "F" => R.family.labels.level 4

private theorem date (R:Run G) (simple:G.Simple):
    ∃ A:ℝ,0<A ∧ ∀m,1+‖R.family.S.scale m‖≤A*R.family.path.levels.clock.hatBeta m := by
  let L:=R.family.path.levels
  let s:=G.slopeConstant
  have sp:0<s:=Gauge.slopeConstant_pos simple
  let a:=1+‖L.clock.bar‖
  have ap:0<a:=by dsimp only [a];positivity
  refine ⟨1+a/s,by positivity,?_⟩
  intro m
  let b:=L.clock.hatBeta m
  have bp:1≤b:=(L.fits.delayed m).le
  have h:s*L.S.scale m=b-L.clock.bar:=by dsimp only [Calendar.hatBeta,b,s];ring
  have cost:s*‖L.S.scale m‖≤b*a:=by
    calc _=‖s*L.S.scale m‖:=by rw [norm_mul,Real.norm_of_nonneg sp.le]
         _=‖b-L.clock.bar‖:=by rw [h]
         _≤‖b‖+‖L.clock.bar‖:=norm_sub_le ..
         _≤b*a:=by
           rw [Real.norm_of_nonneg (zero_le_one.trans bp)]
           dsimp only [a]
           nlinarith only [mul_nonneg (sub_nonneg.mpr bp) (norm_nonneg L.clock.bar)]
  have pricing:‖L.S.scale m‖≤b*a/s:=(le_div_iff₀ sp).2 (by simpa only [mul_comm s ‖L.S.scale m‖] using cost)
  change 1+‖L.S.scale m‖≤(1+a/s)*b
  exact (add_le_add bp pricing).trans_eq (by ring)

theorem physical (simple:G.Simple) (K:ℕ) (μ:ℝ) :
    ∃C:ℝ,0<C ∧ ∃e:ℕ,∀{m N per:ℕ}(_ : R.family.ref 4 ≤ m)(life:m ≤ N)(z:Stock B)(k:ℕ),k ≤ K→
      ∀o:Site (R.family.side m per),
      let q:=charged W Q life o z (μ-R.family.S.scale m) k
      let fare:=(R.family.S.a m)^4*(C*R.family.path.levels.clock.hatBeta m^e*amount B z)
      q.Format o R.family.params (R.family.path.rep N per m) ∧
      q.remBound o (R.family.path.rep N per m) (safety R.family m) fare ∧ (F).coeffSize q.x≤fare :=by
  obtain ⟨c,cp,e,bankCost⟩:=WilsonReportingMeasuredWardIntakePrice.before R Q K μ
  obtain ⟨a,ap,currency⟩:=date R simple
  refine ⟨c*a^e,by positivity,e,?_⟩
  intro m N per age life z k hk o q fare
  let x:=seed (R:=R) Q m per z (μ-R.family.S.scale m) k
  let v:=bank R Q m z (μ-R.family.S.scale m) k
  have raw:=WilsonReportingGuardedSource.purchased W life age o 4 x
  have amountPos:0≤amount B z:=add_nonneg (norm_nonneg _) (sum_nonneg fun _ _=>norm_nonneg _)
  have vc:(F).coeffSize v≤(c*a^e)*R.family.path.levels.clock.hatBeta m^e*amount B z:=by
    refine (bankCost m _ k hk z).trans ?_
    calc
      _ ≤ c*(a*R.family.path.levels.clock.hatBeta m)^e*amount B z:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (currency m) _) cp.le) amountPos
      _ = _:=by rw [mul_pow];ring
  have sx:(F).coeffSize x≤fare:=by
    change (F).coeffSize (seed (R:=R) Q m per z (μ-R.family.S.scale m) k)≤_
    rw [seed,frame R Q m per age,Extra.Histories.Size.smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (R.family.S.a_pos m).le]
    exact mul_le_mul_of_nonneg_left vc (pow_nonneg (R.family.S.a_pos m).le _)
  exact ⟨raw.1,Extra.Histories.rem_mono raw.2.1 ((Work.G08.size_core F x).trans sx),raw.2.2.1.symm ▸ sx⟩

end YM.Integration.WilsonReportingMeasuredWardFunding
