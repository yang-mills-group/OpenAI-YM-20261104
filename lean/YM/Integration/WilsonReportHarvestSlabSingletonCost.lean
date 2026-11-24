import YM.Integration.WilsonReportHarvestSlabSingletonClinic
import YM.Integration.WilsonReportHarvestSlabShiftSelected
import YM.Integration.WilsonAllDateHarvestRebook

/-! Spend the actual charged input at the top. Each measured singleton,
including its transport to the old held field, has the additional cost
already reserved in the same original ultraviolet receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabSingletonCost
open Finset Filter Function MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open PhysicalNext.Repeat Lotus Legato Next.Rank.Station
open WilsonAllDateHarvestFiledReplay
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

private theorem powers (a v x y:ℝ) (one:1 ≤ a)(big:1 ≤ v)(xp:1 ≤ x)(y0:0 ≤ y) {s d i h:ℕ}
    (sd:s ≤ d)(ih:i ≤ h){B b:ℝ}(b0:0 ≤ b)(sold:b ≤ B){income:ℝ}(pay:income ≤ y*v^(d+2)*v)(ipos:0 ≤ income):
    b*(a*v)^s*income*x^i  ≤  (B*a^d*y)*(v^(2*d+3)*x^h):=by
  have a0:0 ≤ a:=zero_le_one.trans one
  have v0:0 ≤ v:=zero_le_one.trans big
  have x0:0 ≤ x:=zero_le_one.trans xp
  have up:(a*v)^s ≤ a^d*v^d:=by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ one sd) (pow_le_pow_right₀ big sd) (pow_nonneg v0 _) (pow_nonneg a0 _)
  have coeff:=mul_le_mul sold up (pow_nonneg (mul_nonneg a0 v0) _) (b0.trans sold)
  have bnd:b*(a*v)^s*income ≤ B*(a^d*v^d)*(y*v^(d+2)*v):=
    mul_le_mul coeff pay ipos (mul_nonneg (b0.trans sold) (mul_nonneg (pow_nonneg a0 _) (pow_nonneg v0 _)))
  have final:0 ≤ B*(a^d*v^d)*(y*v^(d+2)*v):=mul_nonneg (mul_nonneg (b0.trans sold) (mul_nonneg (pow_nonneg a0 _) (pow_nonneg v0 _))) (mul_nonneg (mul_nonneg y0 (pow_nonneg v0 _)) v0)
  apply (mul_le_mul bnd (pow_le_pow_right₀ xp ih) (pow_nonneg x0 _) final).trans_eq
  rw [show 2*d+3=d+(d+2)+1 by omega];simp only [pow_add,pow_one];ring

theorem original (s:Fin 3→ℕ) (d:ℕ)(levels:∀i,s i ≤ d):
    ∃B:ℝ,0 ≤ B ∧ ∃h:ℕ,∀ (n m t per H:ℕ) (_:n ≤ m) (_:m ≤ t) (S:(i:Fin 3)→Emblems C (s i))
      (P:(i:Fin 3)→Sight C (s i) per) (x:(i:Fin 3)→Palette C (s i)) (B₀:ℕ→ℕ→ℝ),
      (∀i,Spine R.doors B₀ R.makes n per (s i) (t+1) (P i) (S i)) →
      (∀i,size (x i) ≤ WilsonReportHarvestReplayPhysical.allowance R m (t+1) d H) →
      ∀i (z:Site ((C).side n per)) (f:Body),Cap (s i+2) f 1 →
      let F:=Records.clinic C per (t+1) (s i) (Many.point (S i) (x i) m (t+1)) n z (1,false) f
      let price:=B*((C).S.a n/(C).S.a m)^d*((C).path.levels.clock.hatBeta m)^H*
        WilsonAllDateHarvestFixedSpectatorInvoice.extra R m t (2*d+3) h
      (∀U,‖F U‖ ≤ price) ∧ ∀u (age:u ≤ t+1) V,‖actualTransport C (N:=t+1) F age V‖ ≤ price:=by
  choose b b0 e clinic using (fun i=>WilsonReportHarvestSlabSingletonClinic.original R (s i))
  let B:=∑i,b i
  let h:=Finset.univ.sup e
  refine ⟨B,Finset.sum_nonneg (fun i _=>b0 i),h,?_⟩
  intro n m t per H nm mt S P x B₀ admitted bought i z f cap F price
  let a:=(C).S.a n/(C).S.a m
  let v:=(C).S.a m/(C).S.a (t+1)
  let X:=(C).path.levels.clock.hatBeta (t+1)
  have one:1 ≤ a:=(one_le_div ((C).S.a_pos _)).2 ((C).S.strictAnti.antitone nm)
  have big:1 ≤ v:=(one_le_div ((C).S.a_pos _)).2 ((C).S.strictAnti.antitone (mt.trans t.le_succ))
  have xp:1 ≤ X:=((C).path.levels.fits.delayed _).le
  have y0:0 ≤ ((C).path.levels.clock.hatBeta m)^H:=pow_nonneg (zero_le_one.trans ((C).path.levels.fits.delayed _).le) _
  have eq:(C).S.a n/(C).S.a (t+1)=a*v:=by dsimp only [a,v];exact (div_mul_div_cancel₀ ((C).S.a_pos m).ne').symm
  have spine:=WilsonAllDateHarvestRebook.sizeAt (admitted i) nm (mt.trans t.le_succ) le_rfl (bought i)
  have sb:b i ≤ B:=Finset.single_le_sum (f:=b) (fun j _=>b0 j) (Finset.mem_univ i)
  have ie:e i ≤ h:=Finset.le_sup (s:=Finset.univ) (f:=e) (Finset.mem_univ i)
  have total (U):‖F U‖ ≤ price:=by
    have field:=clinic i n (t+1) per (nm.trans (mt.trans t.le_succ)) (Many.point (S i) (x i) m (t+1)) z f cap U
    rw [eq] at field
    exact field.trans (powers a v X _ one big xp y0 (levels i) ie (b0 i) sb spine (Finset.sum_nonneg (fun _ _=>norm_nonneg _)))
  exact ⟨total,fun u age V=>actualTransport_norm_le C R.makes le_rfl total age V⟩

end YM.Integration.WilsonReportHarvestSlabSingletonCost
