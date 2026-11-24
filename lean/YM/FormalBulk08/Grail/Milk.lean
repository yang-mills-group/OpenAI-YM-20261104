import YM.FormalBulk08.Grail.Nim

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Grail
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Tensor
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{E: Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{m d l n:ℕ}{η A : ℝ}{a:Loc G 1}

set_option maxHeartbeats 600000 in
lemma drive_sample (v:edgeL G)(x:Snap G d): fderiv ℝ (Pose.curtain v) 0 x=assigns (Place.sampled x) v:= by
   let L:= EuclideanSpace.proj (𝕜:=ℝ) v.2.2
   let f := Film.sampleIn (Place.seat v.1) (bearing v) (G:=G) (d:=d)
   have he : Pose.curtain (d:=d) v=(L ∘ logo) ∘ f:=rfl
   have h : DifferentiableAt ℝ logo (f 0) := by rw [map_zero];exact (logo_smooth G d).differentiableAt (by simp)
   rw [he,fderiv_comp 0 (L.differentiableAt.comp _ h) f.differentiableAt,map_zero,fderiv_comp _ L.differentiableAt (by rwa [map_zero] at h), ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]; simp_rw [ContinuousLinearMap.comp_apply, Place.echoing]; unfold assigns Place.sampled; simp [L,f,Film.sampleIn]

-- arbitrary tensor homogeneous product of nonconstant fields
lemma collection (U: Fin m → E→ℝ)(h:∀ i,ContDiffAt ℝ ω (U i) 0)(hp:∀ i,U i 0=0): ∀ v : Fin m→E,
    Tensor.coeff (fun x=> ∏ i, U i x) m 0 v=(Fintype.card (Equiv.Perm (Fin m)):ℝ)⁻¹ * ∑ s:Equiv.Perm (Fin m), ∏ i,(fderiv ℝ (U i) 0) (v (s i)) := by
   intro v
   let T := Tensor.coeff (fun x=> ∏ i, U i x) m 0
   let P:= (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin m) ℝ).compContinuousLinearMap (fun i=>fderiv ℝ (U i) 0)
   have he: ContDiffAt ℝ (↑m) (fun x:E=>∏ i,U i x) 0:=(Pose.rack_prod Finset.univ (fun i _=>h i)).of_le le_top
   have hh: T = symmetrize P := by
       apply ext_diag T _ (coeff_symm he) (symmetrize_sym _); funext x
       rw [symmetrize_diagonal]; unfold T; rw [←WardBin.leading_tensor x _ he]; change _=∏ i,(fderiv ℝ (U i) 0) x
       let f (a:ℝ):= a • x; have hf : HasDerivAt f x 0:= by simpa [f] using! ((hasDerivAt_id' (0:ℝ)).smul_const x)
       apply WardBin.leading_of_lim; · exact (show ContDiffAt ℝ m (fun x:E=>∏ i,U i x) (f 0) from (by rw [show f 0=0 from zero_smul ..]; exact he)).comp (f:=f) _ (contDiffAt_id.smul contDiffAt_const)
       have hu i: HasDerivAt (U i ∘ f) ((fderiv ℝ (U i) 0) x) 0:= by
           exact (((h i).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt_of_eq _ hf (show f 0=0 from zero_smul ..).symm
       have hv i : Tendsto (fun t:ℝ=> t⁻¹* U i (f t)) (𝓝[>] (0:ℝ)) (𝓝 ((fderiv ℝ (U i) 0) x)) := by simpa [f,Function.comp_def,hp,smul_eq_mul] using! (hu i).tendsto_slope_zero_right
       have hg:= tendsto_finsetProd (s:=Finset.univ) (fun i _=> hv i)
       exact hg.congr' (.of_forall (fun i=>by simp only [smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,inv_pow];rfl))
   change T v= _; rw [hh, Tensor.symmetrize]; simp [P]

lemma steady_bl (X : Snap G d)(a:ℕ)(h:throughSlot X a): Place.sampled X∈rangeLt (Axis→G.Color) a:= by
   let f : Route G d →L[ℝ] G.Color:= LinearMap.toContinuousLinearMap { toFun := steady, map_add' :=steady_add, map_smul':=fun t x=>?_ }; swap
   · unfold steady; simp [Finset.smul_sum,smul_comm t]
   exact vector_band _ fun i=> linear_band f _ (rations X h i)
lemma stead (X : Snap G d): Place.sampled X∈rangeLt (Axis→G.Color) (d+1):= steady_bl X (d+1) (fun i h=>by have :=i.isLt; omega)

lemma severance (T:Tile (edgeL G) m)(h:Agate T)(hp: Knoxville (fame _) η (0,a) T A)(hs:0<η)(X: Fin m→Snap G d):
    slate T d m X=tariffs (fun i=>assigns (Place.sampled (X i))) T := by
    let I:=Equiv.Perm (Fin m); let S i:=assigns (Place.sampled (X i));
    let f (w:chain (edgeL G) m) (s:I):= T w*∏ i,S (s i) (w i)
    have he s : Summable (fun w=>f w s):= ((pays_product (S ∘ s) a hs (fun i=>shoulder (stead (X (s i))))).choose_spec.2 T A hp).1
    let c:ℝ:=Fintype.card I; have hc:0<c:= by change (0:ℝ)< (Fintype.card (Equiv.Perm (Fin m)):ℝ); positivity
    rw [slate_read a T X hs hp]; change (∑' w,_) = tariffs S T
    have hh (v:chain (edgeL G) m): T v* Tensor.coeff (tier v) m 0 X=c⁻¹*∑ i:I,f v i:= by
       have hv i:Pose.curtain (d:=d) (v i) 0=0:= by unfold Pose.curtain; rw [Film.lane_root]; rfl
       unfold Pose.tier f; rw [collection (fun i=>Pose.curtain (v i)) (fun i=> Pose.curtain_diff _) hv, ←Finset.mul_sum, mul_left_comm]
       simp_rw [drive_sample]; rfl
    simp_rw [hh]; rw [tsum_mul_left, Summable.tsum_finsetSum (fun i _=> he i)]
    have hx (s:I): (∑' v, f v s)=tariffs S T:= tariff_turn S T h s
    simp_rw [hx];simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];change c⁻¹*(c*_)=_;rw [←mul_assoc, inv_mul_cancel₀ hc.ne',one_mul]
end YM.FormalBulk08.Grail
