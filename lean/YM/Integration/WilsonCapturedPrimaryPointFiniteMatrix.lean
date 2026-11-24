import YM.Integration.WilsonCapturedPrimaryPointFundedTail

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPointFiniteMatrix
open Filter Function Finset Lattice Laurent Wilson RG Precision FormalBulk08
open Next.Free Flat Stationary Kemp Pose Gorge Reef Mesa Exterior
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations RG16 RG16.Literal RG16.Guarding
open Pert.Asymptotics Trace.Physical
open WilsonCapturedPrimaryPointBasis WilsonCapturedPrimaryPointRectangle WilsonPointChildFiledPress
open scoped Classical BigOperators Topology ENNReal
variable {G:Gauge}{d D:ℕ}

theorem remaining (F:Frame G d)(Z:Pot G)(row:F.Index)(q:ℕ){B:ℝ}(bp:0≤B)
    (bounded:∀r≤(F.grades row).2,∀e≤q,|pearlJ F (Z e r) row|≤B):
    WilsonCapturedPrimaryPointRectangle.tail F Z row q≤((F.grades row).2+1:ℕ)*(q+1:ℕ)*B:=by
  unfold WilsonCapturedPrimaryPointRectangle.tail
  calc
    _ ≤ ∑r∈range ((F.grades row).2+1),∑e∈range (q+1),B:=by
      apply Finset.sum_le_sum
      intro r hr
      apply (Finset.sum_le_sum (g:=fun _=>B) fun e he=>
        bounded r (by simpa [Nat.lt_succ_iff] using hr) e
          (by simpa [Nat.lt_succ_iff] using (Finset.mem_filter.mp he).1)).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _=>bp)
    _ = _:=by simp [nsmul_eq_mul];ring

/-- Uniform normalized matrix of the complete evaluated rectangular finite-volume program.
The spatial and the coupling truncations are on the same charged point table. -/
theorem original (R:Run G)(L:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (simple:G.Simple)(funded:WilsonPointChildFiledTest.Filed R){u:ℕ→ℕ}
    (announced:WilsonWindowFormalPurchase.Canonical u R.kit)(o:Loc G 1)(q:ℕ):
    ∀ᶠi:ℕ in atTop,∀N per:ℕ,i≤N→∀t:Tour R i,∀row col:(R.family.labels.level d).Index,
      let F:=R.family.labels.level d
      let B:=(R.family.path.rep N per i).p.B
      let n:=R.family.side i per
      let g:=regulatorRun R.family N per i
      let Z:=WilsonOlderFreshPointGauge.field R L a depth i (axis F col) (t,fixed D)
      |finite F n B Z row (q+2) g-(if row=col then 1 else 0)|≤
        (2*((F.grades row).2+1:ℕ)*(q+3:ℕ))*g^q:=by
  classical
  let F:=R.family.labels.level d
  let q':=q+2
  have allSeams:=fun (row:F.Index)(r:Fin ((F.grades row).2+1))=>
    WilsonCapturedPrimaryPointStage.original R L a depth simple funded announced o q' r q row
  have allBounds:=fun (row:F.Index)(r:Fin ((F.grades row).2+1))=>
    WilsonCapturedPrimaryPointFundedTail.original R L a depth simple funded announced o q' r row
  filter_upwards [Filter.eventually_all.mpr (fun row:F.Index=>
    Filter.eventually_all.mpr (allSeams row)),Filter.eventually_all.mpr (fun row:F.Index=>
    Filter.eventually_all.mpr (allBounds row)),R.family.path.levels.fits.deep.eventually (eventually_ge_atTop d),
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (2:ℝ)]
    with i seams bounds trained warm
  intro N per here t row col _ B n g Z
  let β:=R.family.path.β N per i
  have band:=(R.makes.wilson.represents N per i here).band.1
  change R.family.path.levels.clock.hatBeta i/2≤β at band
  have one:1≤β:=by linarith only [band,warm]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le one))
  have small:g≤1:=inv_le_one_of_one_le₀ (show 1≤Real.sqrt β by simpa using Real.sqrt_le_sqrt one)
  have hfront:=trained.trans (R.family.path.levels.fits.mono (Nat.le_succ _))
  have deposit:coordinate F Z row=(if row=col then 1 else 0):=
    (WilsonCapturedPrimaryPointBasis.original R L a depth i t simple o hfront row col).1
  have cut:=calibrated F Z row col q' gp.le small deposit
  have seam' := seam F n B Z row q' gp.le small (pow_nonneg gp.le q)
    (fun r hr e he=>seams row ⟨r,Nat.lt_succ_of_le hr⟩ N per here t col e he)
  have tail':=remaining F Z row q' (pow_nonneg (inv_nonneg.mpr gp.le) 3)
    (fun r hr e he=>bounds row ⟨r,Nat.lt_succ_of_le hr⟩ N per here t col e he)
  let W:ℝ:=((F.grades row).2+1:ℕ)*(q'+1:ℕ)
  have credit:g^(q'+1)*(W*(g⁻¹)^3)=W*g^q:=by dsimp [q'];rw [show q+2+1=q+3 by omega,pow_add];field_simp
  have bills:=cut.trans ((mul_le_mul_of_nonneg_left tail' (pow_nonneg gp.le _)).trans_eq credit)
  calc
    _ ≤ |finite F n B Z row q' g-rectangle F Z row q' g|+
        |rectangle F Z row q' g-(if row=col then 1 else 0)|:=abs_sub_le _ _ _
    _ ≤ W*g^q+W*g^q:=add_le_add seam' bills
    _ = _ := by dsimp [W,q'];push_cast;ring

end YM.Integration.WilsonCapturedPrimaryPointFiniteMatrix
