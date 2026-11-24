import YM.GradedFar.Moving.Cap
/-!
# Resolve trial error through the Screen equation's native finite tangent
No guess on lower sectors (every grade from it).
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
private def chairMove : MoveSpace G d →ₗ[ℝ] Maps G d :=
    ((chairs G d).restrictScalars ℝ).toLinearMap ∘ₗ (Normalize.Change G d).subtype ∘ₗ (guide G d).symm.toLinearMap
private lemma chairMove_eq (B : Normalize.Change G d) : chairMove (guide G d B)= chairs G d B.val := by
    unfold chairMove; simp_rw [LinearMap.comp_apply]; change chairs G d ((guide G d).symm _).val=_; rw [LinearEquiv.symm_apply_apply]
private lemma guide_θ (u:I→Normalize.Change G d) (h : Tendsto (fun i=>chairs G d (u i).val) T (𝓝 0)) : Tendsto (fun i=> guide G d (u i)) T (𝓝 0) := by
    let A := chairMove (G:=G) (d:=d)
    let B:= A.leftInverse
    have ht : LinearMap.ker A = ⊥ := LinearMap.ker_eq_bot.mpr ((chairs G d).injective.comp (Subtype.val_injective.comp ((guide G d).symm.injective)) : Injective A)
    rw [← B.map_zero]
    apply (B.continuous_of_finiteDimensional.continuousAt.tendsto.comp h).congr
    intro i; change B (chairs _ _ _) = _; rw [←chairMove_eq]; exact LinearMap.leftInverse_apply_of_inj ht _

variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ i,z i∈Growth.Small) {simple : G.Simple}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
  {Z : Rolled G d} (hZ : Righted Z) {F : Pose.Plans G d}
variable (θ : ℝ→ℝ) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1)) (h : Beginning N θ d F)
local notation "W"=> compareZ N M θ Z p
local notation "x'"=> fun i=> resize (r i) (z i)
variable (Y : ℝ → Prediction G d) (hy : Held N Y F) (he : refit Z F)

-- Adaptation at generic warmed purses of the lower bound proof
lemma settles {Z : I→Prediction G d} (D : Fray (N.store.measure d)) (h0 : D.Via Z (u:=T))
    (x:I→Normalize.Change G d) (hx:Tendsto (fun i=> guide G d (x i)) T (𝓝 0)) :
    ∀ᶠ i in T, ‖guide G d (x i)‖ ≤ 2 * ‖guide G d ((N.store.measure d).D (recruit (stand (x i)) (Z i)) -
        (N.store.measure d).D (Z i))‖ := by
  let v i:= guide G d (x i); let P i:= D.purse (Z i)
  have hh := (hasStrictFDerivAt_iff_isLittleO.mp (D.fair.contDiffAt.hasStrictFDerivAt (by simp) : HasStrictFDerivAt _ _ D.opening)).def' (by norm_num : (0:ℝ)<1/2)
  have a : Tendsto (fun i=> (P i,v i)) T (𝓝 D.opening) := h0.prodMk_nhds hx
  have b : Tendsto (fun i=> (P i,(0:MoveSpace G d))) T (𝓝 D.opening) := h0.prodMk_nhds tendsto_const_nhds
  filter_upwards [(a.prodMk_nhds b).eventually hh.bound] with i hi
  let A := D.itinerary (P i,v i); let B := D.itinerary (P i,0)
  let L := fderiv ℝ D.itinerary D.opening
  change ‖A-B-L ((P i,v i)-(P i,0))‖ ≤ _*‖(P i,v i)-(P i,0)‖ at hi
  have hf (x : MoveSpace G d) : L (0,x)=x := show D.delta D.opening x=x from by rw [D.unpin (N.store.prepared d)]; rfl
  rw [show (P i,v i)-(P i,0)=(0,v i) from Prod.ext (by exact sub_self _) (by exact sub_zero _), hf, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hi
  have he : A=guide G d ((N.store.measure d).D (recruit (stand (x i)) (Z i))) := by
    unfold A P v; rw [D.way,Fray.box,LinearEquiv.symm_apply_apply]
  have hu : B=guide G d ((N.store.measure d).D (Z i)) := by
    unfold B P; rw [D.way, Fray.box,map_zero,stand0,Screen.recruit_one]
  rw [map_sub,← he,← hu]; have hV:=norm_add_le (v i-(A-B)) (A-B)
  rw [sub_add_cancel, norm_sub_rev] at hV
  change ‖v i‖ ≤ _; linarith only [hi,hV]

include h H hr hz ht he hZ hy
lemma outlay : Buys T (fun i=> chairs G d (compareZ N M θ Z p (r i) (z i))-1) (g ∘ r) (p+1) := by
    let A i:= W (r i) (z i); let X i:=A i-1; let U (i:I): Normalize.Change G d:= if h:X i∈Normalize.Change G d then ⟨X i,h⟩ else 0
    have hA : ∀ᶠ i in T,A i=stand (U i) := by
      filter_upwards [hr.eventually hZ.1] with i h
      have he : permissible (A i) := permissible.times ((h (z i) (hz i)).inverse (tilted_out Z (r i) (z i)) (tilted_on Z (r i) (z i))) (trial_permitted N M H p _ _)
      exact (by dsimp only [U]; rw [dif_pos (show X i ∈Normalize.Change G d from he)]; exact he.stood_as.symm)
    have hX : ∀ᶠ i in T, A i-1=(U i).val := hA.mono fun i h=> by rw [h]; unfold stand; abel
    have hs := settles T N (N.store.survey d) (Z:=fun i=> Y (resize (r i) (z i)))
      ((warmth N M H θ h Y hy (N.store.survey d)).comp (span_nears T N M r z hr (Eventually.of_forall hz) H)) U
      (guide_θ T U ((sensed_op T N M r z hr hz H hZ θ ht (p:=p)).congr' (hX.mono fun i he=> congrArg (chairs _ _) he)))
    let L:= LinearMap.toContinuousLinearMap (chairMove (G:=G) (d:=d))
    obtain ⟨C,hC,hw⟩:= (screened T N M r z hr hz H hZ θ ht h Y hy he (N.store.survey d) (p:=p)).exists_pos
    apply IsBigO.of_bound (‖L‖*(2*C)); filter_upwards [hA, hX,hs, hw.bound, (span_nears T N M r z hr (Eventually.of_forall hz) H).eventually hy.fixed] with i hA hX hh hw hy
    have hy' := hh.trans (show 2 * _ ≤ 2*(C * ‖(g∘r) i^(p+1)‖) from (by rw [hy, ← hA]; exact mul_le_mul_of_nonneg_left hw (by norm_num)))
    rw [← chairs_one (G:=G) (d:=d), ← map_sub (chairs G d)]; change ‖chairs G d (A i-1)‖ ≤ _
    rw [hX, ← chairMove_eq]
    exact (ContinuousLinearMap.le_opNorm L _).trans ((mul_le_mul_of_nonneg_left hy' (norm_nonneg L)).trans_eq (by ring))

/-- W_s columns themselves thus priced in W_r by the trial fields. -/
lemma covered : Pays T (fun i=> Zenith Z (r i) (z i)) (fun i=> names (train N M d (z i))) (g∘r) p (fun i=> (θ (r i):ℂ)) := by
    refine ⟨train_lin T N M r z (Eventually.of_forall hz) H,?_⟩
    let A i:= Zenith Z (r i) (z i)
    have he:=times_cost T (weak_bound_out T N M r z hr hz H hZ) (outlay T N M r z hr hz H hZ θ ht h Y hy he (p:=p)); rw [zero_add] at he
    refine he.neg_left.congr_left (fun i=>?_)
    rw [mul_sub, mul_one,← column_by,compareZ,chairs_mul,← mul_assoc]
    change -(Zenith Z (r i) (z i)*downward Z (r i) (z i)*_- _) = _; rw [(inverse_ok ..).1, one_mul, neg_sub]; rfl
end
end YM.FVA2.GradedFar.Moving
