import YM.XSpace.Hug

/-!
# The singlet orbit is locally rigid. Keep the actual direction geometry, label by label.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter MeasureTheory Maxwell Maxwell.Free
open scoped BigOperators Topology Classical RealInnerProductSpace ContDiff
variable {G : Gauge} {p : WickPol G} {d : ℕ}
section cluster
variable (g:G.Simple) {f:ℕ→ TaylorTower G→ℂ} (H : ∀ i, Singlet (f i)) (h : p∈shellSector G d)
    (Y:ℕ→Motor G) (he:∀ i,Y i∈ Crown p (f i)) (hf: ∀ T,Tendsto (fun i=> f i T) atTop (𝓝 (probe T p))) (hn:∀ i, nearest p (Y i))

lemma tag_rot (M N:Motor G) (T:TaylorTower G): tag p (M*N) T=tag p M (motor N T):= rfl
include he hf hn in
lemma jaw {V:Motor G} (ht:Rot V) (hY:Tendsto Y atTop (𝓝 V)): V=1:=by
  have hh (T:TaylorTower G): tag p V T=probe T p:= by
    refine tendsto_nhds_unique_of_eventuallyEq (((travel_smooth p T).continuous.tendsto V).comp hY) (hf T) ?_; exact Eventually.of_forall fun i=> congr_fun (he i).2 T
  obtain ⟨W,hW,hw,hw'⟩:=ht.revert
  have hK (T:TaylorTower G): tag p W T=probe T p:=by rw [← show probe (motor W T) p=tag p W T from rfl,← hh (motor W T),← tag_rot,hw]; rfl
  have hs : ‖V-1‖≤0:=by
    have heV := ((tendsto_const_nhds (x:=W)).mul hY |>.sub (tendsto_const_nhds (x:=(1:Motor G)))).norm; rw [hw',sub_self,norm_zero] at heV
    refine le_of_tendsto_of_tendsto' ((hY.sub (tendsto_const_nhds (x:=(1:Motor G)))).norm) heV (fun i=>?_)
    let U:=Y i; have eK : Rot U:= (he i).1; have hm : W*U∈ Crown p (tag p U):= ⟨hW.multiply eK, funext fun T=> (tag_rot W U T).trans (hK (motor U T))⟩
    exact hn i (W*U) hm
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hs)
include he hf hn H h g in
lemma same : ∃ i:ℕ,Y i=1:=by
  by_contra h0; push Not at h0
  obtain ⟨V,hV,q,hq,hE⟩:=rot_set.tendsto_subseq fun i=> (show Y i∈ setOf Rot from (he i).1)
  let k:=Y ∘ q
  have ht : V=1:=jaw k (f:=f ∘ q) (fun i=> he (q i)) (fun i=> (hf i).comp hq.tendsto_atTop) (fun i=> hn _) hV hE
  subst V
  obtain ⟨Z,hz,b,hb,hB⟩:= (isCompact_sphere (0:Motor G) 1).tendsto_subseq fun i=> (show inspect k 1 i∈ Metric.sphere (0:Motor G) 1 from by
    rw [Metric.mem_sphere,dist_zero_right,inspect,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),inv_mul_cancel₀]; exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (h0 _)))
  apply no_arrival (k ∘ b) Z g h (fun i=> (he _).1) ?_ (fun i=> h0 _) (fun i=> hn _) (hE.comp hb.tendsto_atTop) hB
  intro i; change Singlet (tag p (Y (q (b i)))); rw [(he _).2]; exact H _
end cluster
lemma local_sing (g:G.Simple) (h : p∈shellSector G d) (y:ℝ→TaylorTower G→ℂ) (hp: ∀ i, Singlet (y i)) (he:∀ i,(Crown p (y i)).Nonempty)
    (hv: ∀ T,Tendsto (fun t=> y t T) (𝓝 0) (𝓝 (probe T p))): ∀ᶠ t in 𝓝 0,y t=fun T=> probe T p :=by
  by_contra hq; have hr: ∃ᶠ t in 𝓝 0,y t≠ fun T=>probe T p:= fun h=>hq (h.mono fun x hx=> Classical.byContradiction hx)
  obtain ⟨u,hu,ho⟩:= exists_seq_forall_of_frequently hr
  choose K hK hc using fun i:ℕ=> hugging (he (u i))
  obtain ⟨i,hi⟩:=same g (f:= y ∘ u) (fun i=> hp (u i)) h K hK (fun T=> (hv T).comp hu) hc
  apply ho i; rw [← (hK i).2,hi]; rfl
end YM.XSpace.Sample
