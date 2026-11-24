import YM.Integration.WilsonReportingRegisteredWindows
import YM.Integration.WilsonReportHarvestSlabShiftReceipt
import YM.RG05Readout.Pulse.Writer

/-! Cost of one genuine finite ultraviolet mark after its engineering scale
is restored. The exponent is the maximal actual angular degree in that fixed
palette. The Wilson period is chosen after the bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabSingletonBasis
open Finset Filter Function MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open PhysicalNext.Repeat Lotus Legato Next.Rank.Station
open scoped Topology ContDiff Classical BigOperators
open private inverse_threshold from YM.Integration.WilsonReportingRegisteredWindows
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

private theorem basis {d:ℕ}{F:Frame G d} (i:F.Index) (t:ℝ):
    F.scaled t (Size.axis F i)=((t^(F.grades i).2:ℝ):ℂ) • Size.axis F i:=by
  funext j
  by_cases h:j=i
  · subst j
    simp [Size.axis]
  · simp [Size.axis,h]

theorem original (d:ℕ):∃B:ℝ, 0≤B ∧ ∃h:ℕ,∀N per (v:Palette C d) (a:Address.Mark C d)
    (x:Site ((C).side N per)) (U:Config G ((C).side N per)),
    ‖Pulse.key C N per d v a x U‖ ≤ ‖val v a‖*(B*((C).path.levels.clock.hatBeta N)^h):=by
  let angle (a:Address.Mark C d):ℕ:=(((C).labels.level (kept a.1)).grades a.2).2
  let h:=Finset.univ.sup angle
  have bound (a:Address.Mark C d):∃b:ℝ,0≤b ∧ ∀V:CoverConfig G,
      ‖((C).localSection (kept a.1)).evaluate (Size.axis ((C).labels.level (kept a.1)) a.2) V‖ ≤ b:=by
    obtain ⟨c,cost⟩:=(Envelope.compactC (((C).localSection (kept a.1)).continuous_evaluate
      (Size.axis ((C).labels.level (kept a.1)) a.2))).cost
    exact ⟨max 0 c,le_max_left ..,fun V=>(cost V).trans (le_max_right ..)⟩
  choose b b0 cost using bound
  let B:=∑a,b a
  have B0:0≤B:=Finset.sum_nonneg fun a _=>b0 a
  refine ⟨B,B0,h,?_⟩
  intro N per v a x U
  let A:=(C).path.rep N per N
  let θ:=A.p.threshold
  let X:=(C).path.levels.clock.hatBeta N
  let F:=(C).labels.level (kept a.1)
  let T:=(C).localSection (kept a.1)
  let W:=Lattice.pull (1:Signed) x U
  have pos:0<θ:=A.p.threshold_pos
  have one:1≤X:=((C).path.levels.fits.delayed N).le
  have power:(θ⁻¹)^angle a≤X^h:=
    (pow_le_pow_left₀ (inv_nonneg.mpr pos.le) (inverse_threshold R per (show N≤N from le_rfl)) _).trans
      (pow_le_pow_right₀ one (Finset.le_sup (s:=Finset.univ) (f:=angle) (Finset.mem_univ a)))
  have mass:‖T.places (Size.axis F a.2) 0 W‖≤B:=(cost a (expandAt 0 W)).trans
    (Finset.single_le_sum (f:=b) (fun i _=>b0 i) (Finset.mem_univ a))
  change ‖val v a*T.places (F.scaled θ⁻¹ (Size.axis F a.2)) 0 W‖≤_
  rw [basis]
  change ‖val v a*T.evaluate (_ • Size.axis F a.2) (expandAt 0 W)‖≤_
  rw [T.eval_linear.map_smul]
  change ‖val v a*((((θ⁻¹)^angle a:ℝ):ℂ)*T.places (Size.axis F a.2) 0 W)‖≤_
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr pos.le) _)]
  exact mul_le_mul_of_nonneg_left ((mul_le_mul power mass (norm_nonneg _) (pow_nonneg (zero_le_one.trans one) _)).trans_eq (mul_comm ..)) (norm_nonneg _)

end YM.Integration.WilsonReportHarvestSlabSingletonBasis
