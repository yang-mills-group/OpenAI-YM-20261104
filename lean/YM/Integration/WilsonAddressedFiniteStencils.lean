import YM.Integration.WilsonAddressedThermometerBasis
import YM.Integration.WilsonCapturedPrimaryWardRetimed

/-! The paid full physical print of a finite heterogeneous roster at every date of its common upper collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedFiniteStencils
open Function Filter Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOffsetLedger
open WilsonAddressedReportedColumns WilsonInvariantActionPosition
open WilsonAddressedThermometerBasis (Entry coefficient fee)
open WilsonCapturedPrimaryWardRetimed (ratio norm_ratio)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)

abbrev Choices (J:Finset I):=(i:J)→Entry R.family (d i.val)

theorem original (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (K:ℕ):
    ∀ᶠ m:ℕ in atTop,∀(N p:ℕ)(mn:m≤N)(z:I→Site (R.family.side N p)),
      ∃ (Q:∀i,Sight R.family (d i) p) (r:∀i,Emblems R.family (d i)),
        (∀i,Enrolled R.makes R.doors (cash R) m N p (d i) (digits R N p (z i)) (Q i) (r i)) ∧
        ∀(y:∀i,Palette R.family (d i)) (u:ℕ)(mu:m≤u)(un:u≤N),u≤berth R K m →
        let S:=R.family.path.rep N p u
        let h:=fun i=>WilsonCapturedPrimaryWardRetimed.lift (r i) mu (y i)
        ∃q:∀i,Palette R.family (d i),
          (∀i,WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) un (h i)=
            WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) mn (y i) ∧
            Printed R.family (d i) S 0 (kappa R.family.path u) (Q i u (h i)) (q i) (h i)
                (cash R (d i) u*size (h i))) ∧
          ∀J:Finset I,(∑a:Choices R d J,‖∏i:J,coefficient S.p.threshold (q i.val) (a i)‖) ≤
            ∏ i:J,fee R K m (d i.val)*((R.family.S.a m/R.family.S.a u)^(d i.val)*size (y i.val)):=by
  have course:=eventually_all.mpr (fun i:I=>WilsonAddressedCollarPrice.original R simple slow shop (d i) K)
  filter_upwards [course] with m dates N p mn z
  choose Q r enrolled bought using fun i=>dates i N p mn (z i)
  refine ⟨Q,r,enrolled,?_⟩
  intro y u mu un near
  let S:=R.family.path.rep N p u
  let step:=fun i=>ratio R.family m u (d i)
  choose q printed units rows using fun i=>bought i (step i • y i) u mu un near
  refine ⟨q,fun i=>⟨WilsonCapturedPrimaryWardRetimed.lift_read (p:=p) mu un (y i),?_⟩,?_⟩
  · simpa only [WilsonCapturedPrimaryWardRetimed.lift,step,map_smul] using printed i
  · intro J
    have paid (i:I):(∑a:Entry R.family (d i),‖coefficient S.p.threshold (q i) a‖) ≤
        fee R K m (d i)*((R.family.S.a m/R.family.S.a u)^(d i)*size (y i)):=by
      apply (WilsonAddressedThermometerBasis.bill S.p.threshold (q i)).trans
      simpa only [WilsonAddressedThermometerBasis.fee,add_mul,step,size_smul,norm_ratio] using add_le_add (units i) (rows i)
    simp only [norm_prod]
    calc
      _ = ∏i:J,∑a:Entry R.family (d i.val),‖coefficient S.p.threshold (q i.val) a‖ := by
        rw [Finset.prod_univ_sum,Fintype.piFinset_univ]
      _ ≤ _ := Finset.prod_le_prod (fun _ _=>Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (fun i _=>paid i)

end YM.Integration.WilsonAddressedFiniteStencils
end
