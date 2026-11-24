import YM.GradedFar.Moving.Tempo

/-!
# Reinstate the same actual homogeneous frame after reading θ
Now derive the scale action comparison on H for every caller at compact ratio.
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
local notation "ν"=> Teller.logNu 1
local notation "K"=> Kseries N M
local notation "α"=> Measure.adjust N.scheme N.criterion
local notation "ψ"=> GroupS.ψ N.criterion M ν
open Reg.Point (stepV)

variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ i,z i∈Growth.Small) {simple : G.Simple}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
    (θ : ℝ→ℝ) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1)) {Z Z' : Rolled G d} (hZ : Righted Z) {F : Pose.Plans G d} {S : ℝ→ FieldEnd G d}
local notation "ρ"=>fun i=> resize (r i) (z i)

/-- The needed recipe for the *actual* post-normalization orientation. -/
def Layer (S : ℝ→ FieldEnd G d) (Z Z' : Rolled G d) :=
    (∀ᶠ r in τ,∀ s∈Growth.Small, S r * forwards Z' r s = forwards Z r s * S (resize r s)) ∧
    ∀ p : ℕ, Buys τ (fun r=> chairs G d (S r-Continuation.atColumn (Measure.adjust N.scheme N.criterion d) p (θ r))) g (p+1)

variable (h : Beginning N θ d F) (Y : ℝ → Prediction G d) (hy : Held N Y F) (he : refit Z F) (hp : Layer N θ S Z Z')
    (hθ : Buys T (fun i=> (θ (resize (r i) (z i)):ℂ)-
      bend N M (z i) p (θ (r i):ℂ)) (gYM G ∘ r) (p+1))
include H hr hp
lemma primary : Pays T (fun i=> chairs _ _ (S (r i))) (fun _=>names (α d)) (g∘r) p (fun i=> (θ (r i):ℂ)) := by
    cases H
    refine ⟨Till.const T _,?_⟩; simp_rw [← column_by,← map_sub]; exact (hp.2 p).comp_tendsto hr
include hz ht hθ
lemma wear_power : Pays T (fun i=> chairs _ _ (S (ρ i))) (fun i=> names (stepV (ψ (-z i)) (α d)))
    (g∘r) p (fun i=> (θ (r i):ℂ)) := by
    have hf:=Eventually.of_forall (f:=T) hz; let g' i:=g (r i); let u i:ℂ:= θ (r i); let v i:ℂ:= θ (ρ i); let y i:=bend N M (z i) p (θ (r i):ℂ)
    have hm := measuring T N M r hr H θ ht; have hV: Buys T v (g∘r) 1 := charged_theta T N M r z hr hf H θ ht
    let A':= names (α d); have hg:Tendsto (g∘r) T (𝓝 0) := (shrink simple).comp hr
    have hA : Till T (fun _=>A') (g∘r) p := Till.const T _
    have he := flux T N M r z hr hf H θ ht p
    have hh := recrop_substitution T hm hg (psi_lin T N M r z hf H) (fun i=> (tendsK N M H _).start) hA
    simp_rw [composition_names]; refine ⟨shifted T (psi_lin T N M r z hf H) hA, ?_⟩
    have hx:= (primary T N (M:=M) _ (span_nears T N M r z hr hf H) H θ hp (p:=p)).2
    have hb:= hx.trans (show (fun i=>(((g ∘ ρ) i)^(p+1)))=O[T] (fun i=>g' i^(p+1)) from (by
      have hm':=scaled_g T N M r z hr hf H; have hm' : (fun i=>g (ρ i))=O[T] g':= by unfold Buys at hm'; simp_rw [pow_one] at hm'; exact hm'
      exact hm'.pow _))
    let q (k : ℕ) i:= factor (v i) (y i) k
    have hk : Buys T (fun i=> blend A' p (v i)-blend A' p (y i)) (g∘r) (p+1) := by
      let P i:= chord (fun _=> A') p ((v i,y i),0)
      have hu : Continuous (fun t:ℂ × ℂ=> chord (fun _=>A') p (t,0)) := (cont_chord (fun _=>A') (fun _=>continuous_const) p).comp (continuous_id.prodMk continuous_const)
      have hv := hu.continuousAt.tendsto.comp ((collapses T N M r hr H hV le_rfl).prodMk_nhds (show Tendsto y T (𝓝 0) from collapses T N M r hr H he le_rfl))
      have hP : Buys T P (g∘r) 0 := budget T ((hv.norm.eventually_lt_const (lt_add_one _)).mono fun i h=> h.le)
      refine (budget_times_smul T hθ hP).congr_left (fun i=> ?_); exact (tuned_chord (fun _=>A') p 0 (v i) (y i)).symm
    refine ((hb.add hk).add hh).congr_left (fun i=> ?_); dsimp only [A',v,y,bend,u]; abel
include he h hy hZ

omit he h hy hp H ht hθ hz hr hZ in
private lemma lower_one (x : RowSpace G d) (A : Maps G d) (h: ‖A-1‖ ≤ 1/2) : ‖x‖≤2*‖A x‖ := by
  have hh:=( (A-1).le_opNorm x ).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x)); change ‖A x-x‖ ≤ _ at hh
  have ht:=norm_add_le (x-A x) (A x); rw [sub_add_cancel,norm_sub_rev] at ht; linarith only [hh,ht]
/- The genuine layer is almost UNIT, invertible at bounded cost, including at this step. -/
omit he h hy hZ hθ ht hz in
lemma layer_near : Tendsto (fun i=> chairs G d (S (r i))-1) T (𝓝 0) := by
  apply collapses T N M r hr H _ (p:=1) le_rfl
  have hP := primary T N (M:=M) _ hr H θ hp (p:=0)|>.2
  simpa only [blend,names,Nat.zero_add, Finset.sum_range_one,recruited_j N M H (d:=d)|>.zero,chairs_one, pow_zero, one_smul] using hP

omit he h hy hZ hθ ht hz hp H hr in
private lemma cabin {y:I→ℝ} (X L : I→Maps G d) (hn:Tendsto (fun i=>L i-1) T (𝓝 0))
    (hh : Buys T (fun i=>L i*X i) y p) : Buys T X y p := by
  obtain ⟨C,hc,hv⟩:= hh.exists_pos
  apply IsBigO.of_bound (2*C)
  filter_upwards [hv.bound,hn.eventually (Metric.closedBall_mem_nhds (0:Maps G d) (show (0:ℝ)<1/2 by norm_num))]
    with i hi hw
  have hh : ‖L i-1‖ ≤ 1/2 := mem_closedBall_zero_iff.mp hw
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x; calc
      ‖X i x‖ ≤ 2* ‖(L i*X i) x‖ := lower_one (X i x) _ hh
      _ ≤ 2 * (C * ‖y i^p‖ * ‖x‖) := mul_le_mul_of_nonneg_left (le_trans ((L i*X i).le_opNorm _) (mul_le_mul_of_nonneg_right hi (norm_nonneg _))) (by norm_num)
      _ = _ := by ring
set_option maxHeartbeats 250000 in
lemma dressed : Pays T (fun i=> Zenith Z' (r i) (z i)) (fun i=> names (K d (-z i))) (g∘r) p (fun i=>(θ (r i):ℂ)) := by
  let L i:= chairs G d (S (r i)); let P i:= crank N M d (z i) p (θ (r i):ℂ)
  have hQ:= (shrink simple).comp hr; have hm:= measuring T N M r hr H θ ht; have hC:= covered T N M r z hr hz H hZ θ ht h Y hy he (p:=p)
  have hM := K_lin (d:=d) T N M r z (Eventually.of_forall hz) H (p:=p)
  have hs : Pays T P (fun i=> names (K d (-z i))) (g ∘r) p (fun i=>(θ (r i):ℂ)) := ⟨hM,by unfold P crank; simp; exact isBigO_zero ..⟩
  have w := (Pays.joint T hm hQ hC (wear_power T N M r z hr hz H θ ht hp hθ)).2
  have q := (Pays.joint T hm hQ (primary T N (M:=M) r hr H θ hp) hs).2
  have hh : Buys T (fun i=> L i*(Zenith Z' (r i) (z i)- P i)) (g∘r) (p+1) := by
    apply (w.sub q).congr' _ (EventuallyEq.refl ..)
    filter_upwards [hr.eventually hp.1] with i hi
    have ht : L i* Zenith Z' (r i) (z i)= Zenith Z (r i) (z i)* chairs G d (S (ρ i)) := by unfold L Zenith; simp_rw [← chairs_mul,hi _ (hz i)]
    simp only at * -- avoid
    rw [mul_sub, ht, ← revenue_names, ← revenue_names, un_train N M H]; unfold L; abel
  exact ⟨hM, cabin T _ _ (layer_near T N M r hr H θ hp) hh⟩
end
end YM.FVA2.GradedFar.Moving
