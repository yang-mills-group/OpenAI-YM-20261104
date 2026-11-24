import YM.UVExt.SolverLines

/-! Finite-period coercivity at the stationary solve, *not* a uniform implicit radius in cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Set Real Tensor
open scoped Topology ContDiff BigOperators Classical
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

structure LineSolve (A : ℕ→B→B→ℝ) (AL : B→B→ℝ) (r : ℕ→B→ℝ) (R : B→ℝ) (x : ℕ→B) (c : ℝ) : Prop where
  pos : 0<c
  along {k : ℕ→ℕ} {z : B} {y : ℕ→B} (hk : Tendsto k atTop atTop) (hy : Tendsto y atTop (𝓝 z)) (v) : Tendsto (fun i=> A (k i) (y i) v) atTop (𝓝 (AL z v))
  right_side v : Tendsto (fun i=>r i v) atTop (𝓝 (R v))
  subtraction : ∀ᶠ i in atTop,∀ x y z, A i (x-y) z = A i x z - A i y z
  linearity : ∀ᶠ i in atTop,∀ (x:ℝ) y z, A i (x • y) z = x * A i y z
  pays : ∀ᶠ i : ℕ in atTop,∀ y, c*‖y‖^2 ≤ A i y y
  solves : ∀ᶠ i : ℕ in atTop,∀ v, A i (x i) v = r i v

variable {c c' : ℝ} {A A' : ℕ→B→B→ℝ} {AL : B→B→ℝ} {r r' : ℕ→B→ℝ} {R : B→ℝ} {x x' : ℕ→B}
namespace LineSolve
variable (ha : LineSolve A AL r R x c)
include ha
lemma fixed (z v : B) : Tendsto (fun i:ℕ=>A i z v) atTop (𝓝 (AL z v)) := ha.along (v:=v) tendsto_id tendsto_const_nhds
lemma unique {z y : B} (hz : ∀ v, AL z v = R v) (hy : ∀ v, AL y v=R v) : z=y := by
  have hr (v) := tendsto_nhds_unique (ha.fixed (z-y) v) (((ha.fixed z v).sub (ha.fixed y v)).congr' (ha.subtraction.mono fun i hi=> (hi z y v).symm))
  have hv : c*‖z-y‖^2 ≤ AL (z-y) (z-y) := ge_of_tendsto (ha.fixed ..) (ha.pays.mono fun i hi => hi _)
  rw [hr,hz,hy,sub_self] at hv
  by_contra hne; have hr : 0 < ‖z-y‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hne); exact not_le_of_gt (by positivity [ha.pos]) hv
lemma limit_solves {k : ℕ→ℕ} {z : B} (hk : Tendsto k atTop atTop) (ht : Tendsto (x ∘ k) atTop (𝓝 z)) (v) : AL z v=R v :=
   tendsto_nhds_unique (ha.along hk ht v) (((ha.right_side v).comp hk).congr' (hk.eventually ha.solves |>.mono fun i hi=>(hi v).symm))

variable [FiniteDimensional ℝ B]
lemma bounded_sol : ∃ C : ℝ, ∀ i, x i ∈ Metric.closedBall (0:B) C := by
  by_contra! he
  simp_rw [Metric.mem_closedBall,dist_zero_right,not_le] at he
  have hx i := Finset.sum_nonneg (s:=Finset.range i) (fun j _=>norm_nonneg (x j))
  choose N hN using fun n : ℕ => he ((n:ℝ) + ∑ j∈Finset.range n,‖x j‖)
  have hr : Tendsto (fun i=>N i) atTop atTop := tendsto_atTop_mono (f:=id) (fun i=>by
      change i≤_
      by_contra! ht
      have hs := Finset.single_le_sum (s:=Finset.range i) (fun j _=> norm_nonneg (x j)) (Finset.mem_range.mpr ht)
      linarith [Nat.cast_nonneg (α:=ℝ) i,hN i]) tendsto_id
  have ht := tendsto_atTop_mono (f:=fun i:ℕ=> (i:ℝ)) (g:=fun i=> ‖x (N i)‖) (fun i=>show _ by linarith [hN i,hx i]) tendsto_natCast_atTop_atTop
  let v : ℕ→B := fun i=>‖x (N i)‖⁻¹ • x (N i)
  have hspos (i : ℕ) : 0 < ‖x (N i)‖ := by linarith [Nat.cast_nonneg (α:=ℝ) i,hN i,hx i]
  obtain ⟨p,hp,k,hk,hv⟩ := (ProperSpace.isCompact_closedBall (0:B) 1).tendsto_subseq (fun (i:ℕ)=> show v i∈_ by simp [Metric.mem_closedBall,dist_zero_right,v,norm_smul, inv_mul_cancel₀ (ne_of_gt (hspos i))])
  have hz (d) := ha.along (v:=d) (hr.comp hk.tendsto_atTop) hv
  have hm (d : B) : Tendsto (fun i:ℕ=> A (N (k i)) (v (k i)) d) atTop (𝓝 0) := by
     -- have h₀ := ht.comp hk.tendsto_atTop |>.inv_tendsto_atTop -- find
     have hs := ((tendsto_inv_atTop_zero.comp (ht.comp hk.tendsto_atTop)).mul (((ha.right_side d).comp hr).comp hk.tendsto_atTop))
     rw [zero_mul] at hs
     exact hs.congr' (((hr.comp hk.tendsto_atTop).eventually (ha.solves.and ha.linearity)).mono fun i hi=> by dsimp only [Function.comp_apply,v]; dsimp only [Function.comp_apply] at hi; rw [hi.2,hi.1])
  have hL : ∀ d, AL p d=0 := fun d => tendsto_nhds_unique (hz d) (hm d)
  have ho : c*‖p‖^2 ≤ AL p p := ge_of_tendsto (ha.fixed ..) (ha.pays.mono fun i hi => hi p)
  have hD : ‖p‖=1 := tendsto_nhds_unique hv.norm (show Tendsto (fun i=>‖(v∘k) i‖) atTop (𝓝 1) from tendsto_const_nhds.congr fun i=>by simp [v,inv_mul_cancel₀ (ne_of_gt (hspos (k i))),norm_smul])
  rw [hD,hL] at ho -- simplify
  exact not_le_of_gt ha.pos (by simpa using ho)

lemma harvest : ∃ y : B, Tendsto x atTop (𝓝 y) := by
  obtain ⟨C,Q⟩ := ha.bounded_sol
  obtain ⟨p,-,k,hk,hp⟩ := (ProperSpace.isCompact_closedBall (0:B) C).tendsto_subseq Q
  have hz := ha.limit_solves hk.tendsto_atTop hp
  refine ⟨p, Next.Free.UV.must_follow fun f hf=> ?_⟩
  obtain ⟨u,-,g,hg,hu⟩ := (ProperSpace.isCompact_closedBall (0:B) C).tendsto_subseq (fun j : ℕ=> Q (f j))
  have hx := ha.unique hz (ha.limit_solves (hf.comp hg.tendsto_atTop) hu)
  exact ⟨g,hg,hx ▸ hu⟩

lemma same_answer (hb : LineSolve A' AL r' R x' c') : ∃ z,Tendsto x atTop (𝓝 z) ∧ Tendsto x' atTop (𝓝 z) := by
  obtain ⟨z,hz⟩ := ha.harvest; obtain ⟨w,hw⟩ := hb.harvest
  exact ⟨z,hz,(ha.unique (ha.limit_solves (tendsto_id) hz) (hb.limit_solves tendsto_id hw)) ▸ hw⟩
end LineSolve
end YM.UVExt.Paths
