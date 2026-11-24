import YM.Integration.FVA1Physical.Wilson.DistributedIdentity

/-! Uniform control of the rescaled stationary point of the unrestricted
conditional Wilson integral by the rescaled physical boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G:Gauge}

theorem stationary_size (A:Mosaic.Issue G) (v:Palisade) (paid:Grants A.v A.pre A.F v 3)
    {D:ℝ} (hD:0 ≤ D) (hg:0 < A.fClock)
    (small:A.fClock*D < v.initial) (unit:A.fClock*D ≤ 1)
    (z:Positions (Primary A.c G)) (hz:‖z‖ ≤ A.fClock*D) :
    ‖bulkPoint A z‖ ≤ (1+ceilingP v+shade G)*D := by
  let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
  let a:=A.fClock*D
  have a0:0 ≤ a:=mul_nonneg hg.le hD
  have pos:0 ≤ ceilingP v:=by unfold ceilingP; positivity
  have vert:‖ν‖ ≤ ceilingP v*a := (terror A.F A.v v z paid hz small).trans (sail v a0 unit)
  have other (i:Key A.F G) : |bulkCoordinate A z i| ≤ (ceilingP v+shade G)*a := by
    have vv:=clothSize z A.F hz i.1
    change |ν i+(linCash A.F z i.1) i.2| ≤ _
    rw [add_mul]
    exact (abs_add_le ..).trans (add_le_add ((norm_le_pi_norm ν i).trans vert)
      ((PiLp.norm_apply_le _ _).trans vv))
  have bound: ‖bulkCoordinate A z‖ ≤ (ceilingP v+shade G)*a:=
    (pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg pos (shade_pos G).le) a0)).mpr other
  have scale (B:ℝ) : A.fClock⁻¹*(B*a) = B*D:=by dsimp only [a]; field_simp
  have top : ‖A.fClock⁻¹ • z‖ ≤ D:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hg.le)]
    exact (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hg.le)).trans_eq (by field_simp)
  have bottom: ‖A.fClock⁻¹ • bulkCoordinate A z‖ ≤ (ceilingP v+shade G)*D:=by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hg.le)]
    exact (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr hg.le)).trans_eq (scale _)
  rw [bulkPoint,norm_meet]
  exact max_le (top.trans (le_mul_of_one_le_left hD (by linarith only [pos,(shade_pos G).le])))
    (bottom.trans (mul_le_mul_of_nonneg_right (by linarith only) hD))

theorem purchased_stationary_size (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G) {D:ℝ} (hD:0 ≤ D) :
    ∃ M:ℝ, 0 ≤ M ∧ ∀ᶠ x:ℝ in atTop, ∀ (A:Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ∀ z:Positions (Primary A.c G), ‖z‖ ≤ A.fClock*D → ‖bulkPoint A z‖ ≤ M := by
  obtain ⟨v,buy⟩:=purchased_chart_chance J clear simple H H' P K branch hD 0
  have pos:0 ≤ ceilingP v:=by unfold ceilingP; positivity
  refine ⟨(1+ceilingP v+shade G)*D,mul_nonneg (by linarith only [pos,(shade_pos G).le]) hD,?_⟩
  have grow:=Work.E09.betaF_growth G P.L
  have shrink: Tendsto (fun x:ℝ=>D*(2*cue (tip G P.L x))) atTop (𝓝 0):=by
    simpa only [Function.comp_def,zero_mul,add_zero] using (hotel_physical_small v J D 0).comp grow
  filter_upwards [buy,grow.eventually_gt_atTop 0,shrink.eventually (gt_mem_nhds v.first),
      shrink.eventually (gt_mem_nhds zero_lt_one)] with x sale positive reach unit
  intro A patch kernel season z hz
  obtain ⟨paid,_,_,_⟩:=sale A patch kernel season z 0 hz
  have law:=season.case_
  rw [patch] at law
  have band:Mosaic.lensT (tip G P.L x) A.fClock:=Mosaic.ever positive law.beta law.upper
  have hg:0 < A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos positive).trans_le law.beta))
  have sm:A.fClock*D ≤ D*(2*cue (tip G P.L x)) := by
    rw [mul_comm D]; exact mul_le_mul_of_nonneg_right band.2 hD
  exact stationary_size A v paid hD hg (sm.trans_lt reach) (sm.trans unit.le) z hz

end YM.Integration.FVA1Physical.Wilson
