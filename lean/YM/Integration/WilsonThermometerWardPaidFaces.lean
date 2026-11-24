import YM.Integration.WilsonThermometerUnitFilingPaidBlend
import YM.Integration.WilsonThermometerReflectedTwoBills
/-! The actual measured array and its Ward-restored array use the latter's own finite field filing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerWardPaidFaces
open Function Set Filter MeasureTheory Finset Lattice Wilson RG Source Labels OPE OPE.Cards RG12
open Bid RG16 RG16.Literal Trace.Physical.GermGraph Cells MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFeed Next.UVStress Extra.Histories
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {N p b u j:ℕ}

open WilsonThermometerUnitFilingBlend

variable {ι:Type} [Fintype ι] [Nonempty ι] (W:ι→ℂ) (Y:ι→Cut R.family N p)
local notation "big!" => ∑a,W a • Y a

include simple in
theorem original (measured:ι→Cut R.family N p) (smooth:∀a,Continuous (Y a))
    (actual:∀a,Continuous (measured a)) (ju:j≤u) (live:u≤N) (door:Opened R.family 0 u p)
    (price:ι→ℝ) (booked:∀a,Booked R.family N p 0 (Y a) u live)
    (paid:∀a,PaidAt R.family.S N p j (R.family.beta N p) (price a)
        (measured a-report R (Y a) u • (1:Cut R.family N p))):
    Booked R.family N p 0 (big!) u live ∧
    ‖(∑a,W a*R.family.omega N p (measured a))-report R (big!) u‖≤
      ∑a,‖W a‖*price a:=by
  obtain ⟨entered,line⟩:=IntrinsicProductLinearity.booked_sum R.family N p 0 u R.makes door live W Y smooth booked
  refine ⟨entered,?_⟩
  have fitted (Z:Cut R.family N p):report R Z u=(topReport R.family N p 0 R.makes u door live Z) 0:=by
    simp only [report,dif_pos (And.intro door live),terminal R simple (door.post.trans live)]
  have total:report R (big!) u=∑a,W a*report R (Y a) u:=by
    rw [fitted,line];simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
      Finset.sum_congr rfl (fun a (_:a∈Finset.univ)=>congrArg (fun x:ℂ=>W a*x) (fitted (Y a)).symm)
  have each (a):‖R.family.omega N p (measured a)-report R (Y a) u‖≤price a:=by
    let T:=center R.family.S p (ju.trans live) 0
    have edge:=(OPE.Strobe.atone T (R.family.beta N p) (seamless R.makes N p) (paid a).ticket).trans (paid a).mark
    change ‖R.family.omega N p (measured a-report R (Y a) u • (1:Cut R.family N p))‖≤_ at edge
    have exactMean:R.family.omega N p (measured a-report R (Y a) u • (1:Cut R.family N p))=
        R.family.omega N p (measured a)-report R (Y a) u:=by
      unfold Family.omega moment
      simp only [Pi.one_def,Pi.sub_apply]
      rw [integral_sub]
      · simp [probReal_univ]
      · exact (actual a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact integrable_const _
    rwa [exactMean] at edge
  rw [total,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum;intro a _
  rw [←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (each a) (norm_nonneg _)

end YM.Integration.WilsonThermometerWardPaidFaces
