import YM.Integration.WilsonMSDictionaryVector
import YM.RG17.Balance

/-! Only fixed original engineering-grade costs are transferred to the actual positioned
 hierarchy. The finite change of basis is near identity on the same physical radii.
 This pays both all incoming grades and the inverse output, without assuming any extra
 rotational covariance of the positioned subtraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMSDictionaryPositionCost
open Function Filter Set Lattice Wilson Extraction Table Spec PhysicalNext.Repeat.Legato
open RG17 OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (Z : WilsonPrescription G)
    (lead : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ k,∀ᶠ r in trail, Frame.obedient F Y (J r) k) (hG : G.Simple)

abbrev relative (r : ℝ) (k : ℕ) := (homogeneous F J Z r k).trans (J r k).symm

include lead paid hG in
theorem columns (k : ℕ) (x : Free R.family k) :
    Tendsto (fun r=>relative F J Z r k x) trail (𝓝 x) := by
  have same (r : ℝ) : relative F J Z r k x = WilsonPositionPrescribedLift.field F J Z.store k r
      (change F J Z k r x) := by simp only [relative, homogeneous, WilsonPositionPrescribedFrame.positioned,
      LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]; rfl
  simp_rw [same]
  exact WilsonPositionHomogeneousLeading.field F J Z lead paid hG k x

private theorem inverse_near {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (U : ℝ → V ≃ₗ[ℂ] V) (near : ∀ v, Tendsto (fun r=>U r v) trail (𝓝 v)) :
    ∀ᶠ r in trail, ∀ v, ‖(U r).symm v‖ ≤ 2*‖v‖ := by
  let B := Module.finBasis ℂ V
  let e r i := ‖U r (B i)-B i‖
  let c i := ‖(B.coord i).toContinuousLinearMap‖
  have hi i : Tendsto (fun r=> e r i*c i) trail (𝓝 0) := by
    have hz := ((near (B i)).sub (tendsto_const_nhds (x:=B i))).norm.mul_const (c i)
    simpa only [sub_self,norm_zero,zero_mul] using hz
  have small : Tendsto (fun r=> ∑ i,e r i * c i) trail (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _=>hi i)
  filter_upwards [(tendsto_order.mp small).2 (1/2) (by norm_num)] with r price x
  let v := (U r).symm x
  have repr : (U r) v-v = ∑ i,(B.repr v i) • (U r (B i)-B i) := by
    simp only [smul_sub,Finset.sum_sub_distrib,B.sum_repr]
    congr 1
    conv_lhs => rw [←B.sum_repr v,map_sum]
    simp only [map_smul]
  have defect : ‖U r v-v‖ ≤ (∑ i,e r i*c i)*‖v‖ := by
    rw [repr,Finset.sum_mul]
    apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
    rw [norm_smul]
    calc ‖B.repr v i‖ * e r i ≤ (c i*‖v‖)*e r i :=
              mul_le_mul_of_nonneg_right ((B.coord i).toContinuousLinearMap.le_opNorm v) (norm_nonneg _)
         _ = _ := by ring
  have bound := defect.trans (mul_le_mul_of_nonneg_right price.le (norm_nonneg v))
  have rev := norm_sub_rev v (U r v)
  have hv := norm_add_le (v-U r v) (U r v)
  rw [sub_add_cancel] at hv
  rw [←rev] at bound
  have eq : U r v=x := (U r).apply_symm_apply x
  change ‖v‖ ≤ 2*‖x‖
  rw [←eq]
  linarith only [hv,bound]

include lead paid hG in
theorem inverse (k : ℕ) : ∀ᶠ r in trail, ∀ x : S.Field k,
    ‖(homogeneous F J Z r k).symm x‖ ≤ 2*‖(J r k).symm x‖ := by
  filter_upwards [inverse_near (fun r=>relative F J Z r k) (columns F J Z lead paid hG k)] with r bound x
  simpa only [relative,LinearEquiv.symm_trans_apply,LinearEquiv.symm_symm,LinearEquiv.apply_symm_apply] using bound ((J r k).symm x)

include lead paid hG in
/-- Fixed original letters at every physical grade suffice for each positioned moving vector. -/
theorem grades (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (p : ∀ (k : ℕ) (b : Free R.family k) (j : ℕ),
      RateLE RG17.home OPE.run (fun r => Q.cutTest j k (J r k b)) (-(j:ℝ)))
    {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n)→Free R.family (d i)) :
    GradePrice Q d (fun r i=>homogeneous F J Z r (d i) (v i)) (fun _=>0) := by
  intro i j
  rw [add_zero]
  let B := Module.finBasis ℂ (Free R.family (d i))
  let a r b := B.repr (relative F J Z r (d i) (v i)) b
  have rate b : RateLE RG17.home OPE.run (fun r=>a r b) 0 := by
    have limit := (((B.coord b).toContinuousLinearMap.continuous.tendsto (v i)).comp
      (columns F J Z lead paid hG _ (v i))).norm
    exact RateLE.absBound (‖B.repr (v i) b‖+1) RG17.ageLarge
      (((tendsto_order.mp limit).2 _ (lt_add_one _)).mono fun _ hr=>hr.le)
  have each b : RateLE RG17.home OPE.run (fun r=>a r b • Q.cutTest j (d i) (J r (d i) (B b))) (-(j:ℝ)) := by
    simpa only [zero_add] using (rate b).smul (p (d i) (B b) j)
  apply (RateLE.sum RG17.ageLarge (S:=Finset.univ) (fun b _=>each b)).congr
  filter_upwards with r
  have eq : J r (d i) (relative F J Z r (d i) (v i)) = homogeneous F J Z r (d i) (v i) :=
    (J r (d i)).apply_symm_apply _
  rw [←eq,←B.sum_repr (relative F J Z r (d i) (v i)),map_sum,map_sum]
  simp only [a,map_smul]

end YM.Integration.WilsonMSDictionaryPositionCost
