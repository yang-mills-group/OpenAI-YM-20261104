import YM.Integration.WilsonReportHarvestSlabSingletonBasis
import YM.RG05Readout.Flatten.Amass

/-! Uniform-in-period price on the entire original upper single-clinic
field. The count of its actual child sites cancels the inverse fourth power
in the Wilson spatial weight. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabSingletonClinic
open Finset Filter Function MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records RG05Readout.Flatten
open PhysicalNext.Repeat Lotus Legato Next.Rank.Station
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

theorem original (d:ℕ):∃B:ℝ,0≤B ∧ ∃h:ℕ,∀n N per (_:n≤N) (v:Palette C d)
    (z:Site ((C).side n per)) (f:Body),Cap (d+2) f 1 → ∀U:Config G ((C).side N per),
    ‖Records.clinic C per N d v n z (1,false) f U‖ ≤
      B*((C).S.a n/(C).S.a N)^d*size v*((C).path.levels.clock.hatBeta N)^h:=by
  obtain ⟨B,B0,h,price⟩:=WilsonReportHarvestSlabSingletonBasis.original R d
  refine ⟨pulseFee d*B,mul_nonneg (feepos d).le B0,h,?_⟩
  intro n N per top v z f cap U
  let A:=(C).S.toDepth top per
  let X:=(C).path.levels.clock.hatBeta N
  let C₁:=pulseFee d*(B*X^h)
  have X0:0≤X:=zero_le_one.trans ((C).path.levels.fits.delayed N).le
  have key (y:Site ((C).side N per)) (q:Body) (hq:Cap (d+2) q 1):
      ‖stepUp (1,false) y (entrance C d N per v 0 q) U‖ ≤ C₁*size v:=by
    rw [Pulse.entrance_real]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply (norm_sum_le ..).trans
    calc ∑a:Address.Mark C d,‖readJ a.1 0 q*Pulse.key C N per d v a y U‖ ≤
          ∑a:Address.Mark C d,C₁*‖val v a‖:=by
           apply Finset.sum_le_sum;intro a _
           have test:‖readJ a.1 0 q‖≤pulseFee d:=(fees d a.1 box0 hq).trans_eq (mul_one _)
           rw [norm_mul]
           exact (mul_le_mul test (price N per v a y U) (norm_nonneg _) (feepos d).le).trans_eq (by dsimp only [C₁];ring)
         _ = C₁*size v:=by rw [size,Finset.mul_sum]
  have cap' (y:Site A.count):Cap (d+2) (feeR A y f) 1:=
    cap_aff _ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast A.count.property))
      (mapsR A ((C).S.toDepth_odd top per) y) cap
  have bound (y:Site A.count):‖ratioX A d*stepUp (1,false) (A.assemble (z,y))
          (entrance C d N per v 0 (feeR A y f)) U‖ ≤ ‖ratioX A d‖*(C₁*size v):=by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (key _ _ (cap' y)) (norm_nonneg _)
  unfold Records.clinic
  rw [Flatten.lift_pol (hm:=le_rfl) (ht:=top)]
  simp only [Records.like_embed,Records.precinct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply (norm_sum_le ..).trans
  refine (Finset.sum_le_sum (fun y _=>bound y)).trans_eq ?_
  have count:(A.count.val:ℝ)=(C).S.a n/(C).S.a N :=
    (eq_div_iff ((C).S.a_pos N).ne').mpr ((mul_comm ..).trans ((C).S.embeds_scale A))
  have pos:0<(A.count.val:ℝ):=by exact_mod_cast A.count.property
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,site_card,Nat.cast_pow,ratioX,Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (pow_nonneg pos.le _) (pow_nonneg pos.le _))]
  dsimp only [C₁,X]
  rw [←count];field_simp [pos.ne']

end YM.Integration.WilsonReportHarvestSlabSingletonClinic
