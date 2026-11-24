import YM.LocalLTE.Weft.Lumen
/-!
 Local increments halo after global gauge projection. `star` impulses behind projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox.Hall
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open Analysis Slide
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Uniform
variable {G : Gauge} {L c f : Side} {K : KernelChoices} {σ σ' τ τ' ℒ α ν d M : ℝ} {g' : ℝ→ℝ} {q : Teller G}
variable {i j n m:ℕ}
open Weft Tensor
local notation "Xs" => Positions (Uniform.Primary c G)
variable {g:ℝ→ Positions (Uniform.Primary c G)→ℝ} {κ D H :ℝ}
open Frame
lemma framedW (h : Reliable G κ D) (hi:Arp n j M (fun s=> off (g s))) (hv:∀ s∈clip, ContDiff ℝ (↑j) (g s)) {v:ℝ} (hp:v>0)
   (hg: ∀ x:Xs, ‖x‖<v→∀ i:G.El, Brush j H 1 (Frame.convertLinks Chi.canonical κ i ∘ Boulevard.actual) x) : Arp n j ((j.factorial:ℝ)*M * (1+(1+H)*1)^j) (fun s=> Boulevard.stillA (Frame.placed Chi.canonical κ (g s)) ∘ Boulevard.actual) :=by
   let C:= (j.factorial:ℝ)*M*(1+(1+H)*1)^j
   let K(z:Xs)(i:G.El) := Frame.convertLinks Chi.canonical κ i (Boulevard.actual z)
   let F(s:ℝ)(x:Xs) i:= Shellac.off (g s) (K x i)
   have hK(i:G.El): K 0 i=0:=by unfold K Boulevard.actual; rw [map_zero, show represent (0:Bid.Dir G c)=1 from funext (fun i=>by rw [Work.F03.represent_link]; simp)]; exact Hall.boundFlat h i
   have he x : Continuous (K x):= by
         let u₁:=Frame.convertLinks (G:=G) Chi.canonical κ 1 (Boulevard.actual x); have he (i:G.El) : K x i=Frame.adj i u₁:= by unfold K u₁; simpa only [mul_one] using (Frame.motion (x:=i) h (1:G.El) (Boulevard.actual x) (χ:=Chi.canonical));
         rw [funext he]; exact Frame.adj_el u₁
   have hC i (hx:i∈clip) x: Continuous (F i x):= ((hv i hx).continuous.sub continuous_const).comp (he x)
   have hA i:Arp n j C (fun s x=> F s x i):= Arp.splice (hK i) hi (hg 0 (by rw [norm_zero]; exact hp) i)
   have hT(s:ℝ)(hs:s∈clip)(V:Xs): Boulevard.stillA (Frame.placed Chi.canonical κ (g s)) (Boulevard.actual V) = ∫ u,F s V u ∂G.probHaar:=by
      unfold Boulevard.stillA; rw [Frame.meansRead h,Frame.meansRead h]; simp_rw [boundFlat h]; unfold F Shellac.off; simp_rw [Pi.sub_apply]; exact (integral_sub (μ:=G.probHaar) (((hv s hs).continuous.comp (he V)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)).symm
   let P(s:ℝ)(x:Xs):= ∫ u,F s x u ∂G.probHaar
   have hP: Warp n j C P := Warp.load hA (fun s hs=>?_) (fun i h=> Eventually.of_forall fun x=> (hC i h x).measurable) -- edit
   swap
   · -- uniform near across color from continuity K x uniform (adj cost) via control at 1
      obtain ⟨Q,hQ,H'⟩:= Brush.neighborhood 0 ((hv s hs).contDiffAt.sub (contDiffAt_const (c:=(g s 0)))) -- edit
      obtain ⟨r,hr,hu⟩:= Metric.nhds_basis_ball.eventually_iff.mp H'
      have hm : ∀ᶠ y in 𝓝 (0:Xs), Uniform.shade G * ‖K y 1‖ < r := by
         have ht:= (hg 0 (by rw [norm_zero]; exact hp) 1).smooth.continuousAt.norm; have he:= ht.const_mul (Uniform.shade G); exact he (gt_mem_nhds (show Uniform.shade G * ‖K 0 1‖<r from (by rw [hK,norm_zero,mul_zero]; exact hr)))
      refine ⟨(j.factorial:ℝ)*Q*(1+(1+H)*1)^j,?_⟩; filter_upwards [hm, ball_mem_nhds 0 hp] with x hx hx' i; have hh:= hg x (mem_ball_zero_iff.mp hx') i
      have he : K x i=Frame.adj i (K x 1):= by unfold K; simpa only [mul_one] using Frame.motion (χ:=Chi.canonical) h (x:=i) 1 (Boulevard.actual x)
      have H':Brush j Q 1 (Shellac.off (g s)) (K x i):= hu (x:=K x i) (mem_ball_zero_iff.mpr (by rw [he]; exact (Frame.adj i|>.le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_right (Frame.adj_bound i) (norm_nonneg _)).trans_lt hx))) -- edit y
      exact (hh.pine H').trim
   obtain ⟨U,HU,hp'⟩:=hP.hymn; have hΩ : Hex n P:= Hex.invert (fun x=> Weft.integralX (Hex.invert (fun i=> (hA i).hex.use _)) (fun s hs=> (hC s hs x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))
   have hQ:Arp n j C P:= ⟨hΩ,fun s hs=> (HU.brush s hs).shimmy ((hp' s hs).comp_tendsto (show Tendsto (orb (E:=Xs) s) (𝓝 0) (𝓝 0) from (by simpa using! ((orb (E:=Xs) s).continuous.tendsto 0))))⟩
   exact hQ.adjust fun s hs=> (funext (hT s hs)).symm
end YM.LocalLTE.FrameBox.Hall
