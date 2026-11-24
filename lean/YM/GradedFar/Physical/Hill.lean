import YM.GradedFar.Physical.Actual

/-!
# Compact profiles and uniform witnesses for the physical two-zone geometry

Use (same units) at every clearance application.
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon
open Moving Growth Pose Books
open scoped Topology BigOperators Classical
variable {n m d h : ℕ} {I:Type} [Fintype I]

lemma little_walls {α : Type} [TopologicalSpace α] {K : Set α}(F:I→α→E4) (hK:IsCompact K)
    (h : ∀ i, ContinuousOn (F i) K) (ht : ∀ i x, x∈K → F i x≠0) :
    ∃ c : ℝ,0<c ∧ ∀ i:I, ∀ x∈K,c≤ ‖F i x‖ := by
    rcases K.eq_empty_or_nonempty with he|he; · exact ⟨1,zero_lt_one, fun _ x hx=>False.elim (by simp_all)⟩
    choose x hx H using fun i:I=> hK.exists_isMinOn he (h i).norm
    cases isEmpty_or_nonempty I
    case inl hI=> exact ⟨1,zero_lt_one, fun i=> False.elim (isEmpty_iff.mp hI i)⟩
    case inr hI=>
      obtain ⟨i,hi⟩:= Finite.exists_min (f:=fun i=> ‖F i (x i)‖)
      exact ⟨_, norm_pos_iff.mpr (ht i (x i) (hx i)), fun j x hx=> le_trans (hi j) (H j hx)⟩
lemma smooth_hill {K:Set (Points n)}(hK:IsCompact K)(hr:K⊆conf n): ∃ (M δ:ℝ), 0 < M ∧ 0 < δ ∧ ∀ x∈K,
        (∀ i:Fin n, ‖x i‖ ≤ M) ∧ ∀ i j,i≠j→δ≤‖x i-x j‖:= by
    let F (q : {t : Fin n × Fin n// t.1≠t.2})(x:Points n):= x q.val.1-x q.val.2
    obtain ⟨δ,hd,h⟩:= little_walls F hK (fun i=> Continuous.continuousOn (by unfold F; fun_prop))
      (fun i x hx=> sub_ne_zero.mpr fun h=> i.property (hr hx|>.eq_iff.mp h))
    choose M hM using fun i : Fin n=> hK.exists_bound_of_continuousOn (f:=fun x:Points n=> x i) (by fun_prop)
    obtain ⟨B,hb⟩:= Finite.bddAbove_range M
    exact ⟨max B 1,δ,lt_max_of_lt_right zero_lt_one,hd,fun x hx=> ⟨fun i=> le_trans (hM i x hx) ((hb (mem_range_self _)).trans (le_max_left ..)),fun i j ne=> h ⟨(i,j),ne⟩ x hx⟩⟩

structure Terracing (r s M δ:ℝ)(x:Points n)(y:Points m): Prop where
    pos : 0<r
    younger : r≤ s
    xcap : ∀ i, ‖x i‖ ≤ M
    ycap : ∀ i, ‖y i‖ ≤ M
    xsep : ∀ i j,i≠j→δ≤‖x i-x j‖
    ysep : ∀ i j,i≠j→δ≤‖y i-y j‖
    ynear : ∀ i,2*δ≤‖y i‖
    together : r*M≤ s*δ
-- uniform appointment
lemma terrain {K:Set (Points n)} {S:Set (Points m)} (hK:IsCompact K) (hk:K⊆conf n) (hS:IsCompact S) (hs:S⊆ Outside m) :
    ∃ (M δ:ℝ),0<M ∧ 0<δ ∧ ∀ᶠ y in (atTop:Filter ℝ), ∀ (r : ℝ), 0<r → ∀ x∈K, ∀ v∈ S,
          Terracing r (resize r y) M δ x v := by
    have he:S⊆ conf m:= fun x hx=> O.Enh.room (hs hx)
    obtain ⟨M,h,hM,hd,H⟩:= smooth_hill hK hk
    obtain ⟨N,c,hN,hc,hT⟩:= smooth_hill hS he
    obtain ⟨e,hp,hf⟩:= little_walls (fun (i:Fin m)(p: Points m)=> p i) hS (fun i=> by fun_prop) (fun i x hx=> O.Enh.clear (hs hx) i)
    let δ:= min (min h c) (e/2); have hδ:0<δ:= lt_min (lt_min hd hc) (half_pos hp)
    refine ⟨M+N,δ,add_pos hM hN,hδ,?_⟩
    filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop ((M+N)/δ),eventually_ge_atTop (0:ℝ)]
      with t (ht:(M+N)/δ ≤ exp t) ht' r hr x hx v hv
    obtain ⟨X,Y⟩:= H x hx; obtain ⟨L,U⟩:= hT v hv
    refine ⟨hr, ?_, fun i=> by linarith only [X i,hN], fun i=> by linarith only [L i,hM], fun i j ne=> ?_, fun i j ne=> ?_,fun i=> ?_,?_⟩
    · change r≤r*exp t; exact le_mul_of_one_le_right hr.le (Real.one_le_exp ht')
    · exact le_trans (le_min_iff.mp (le_trans (min_le_left ..) (le_refl (min h c))) |>.1) (Y i j ne)
    · exact ((min_le_left ..).trans (min_le_right h c)).trans (U i j ne)
    · have : δ≤e/2:= min_le_right ..; linarith [hf i v hv]
    unfold resize; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hδ).mp ht) hr.le
end
end YM.FVA2.GradedFar.Physical
