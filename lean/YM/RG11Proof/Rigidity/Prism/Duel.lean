import YM.RG11Proof.Rigidity.Prism.Switch

/-!
# Separate one orbit sample from the other
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Prism
open scoped BigOperators Topology
open Function Set MeasureTheory Metric Submodule Filter
variable {I N : Type} [Fintype I]
local notation "X"=>Desk I
local notation "K"=>circle I

/-- A peak known at an INTERIOR point on the first track can't be missed on
the second compact track if the moment equalities hold. -/
private lemma noPeak {f g : X → ℝ} (hf : Continuous f) (hg: Continuous g) {a : X}
    (h : a∈ ball 0 1) {C : ℝ} (he : f a=C) (hp : ∀ x∈K,0≤f x)
    (hQ : ∀ x∈K,0≤g x ∧ g x<C) (hk : ∀ n:ℕ, (∫ x in K,f x^n)=∫ x in K,g x^n) : False := by
  let b := circle I
  have hb : IsCompact b:=isCompact_closedBall ..
  have ha : a∈b := ball_subset_closedBall h
  obtain ⟨z,hz,hZ⟩ := hb.exists_isMaxOn ⟨a,ha⟩ hg.continuousOn
  obtain ⟨r,hr,hs⟩ := exists_between ((hQ z hz).2)
  have hR:= (hQ z hz).1; have hr' : 0<r:= lt_of_le_of_lt hR hr
  have hy : a∈ {x:X|r<f x} ∩ ball 0 1 := ⟨show r < f a from hs.trans_eq he.symm,h⟩
  let T := {x:X|r<f x} ∩ ball 0 1
  have hT : IsOpen T := (isOpen_lt continuous_const hf).inter isOpen_ball
  have hsub : T ⊆ b := inter_subset_right.trans ball_subset_closedBall
  let s := volume.real T
  let t := volume.real b
  have hv : volume T≠⊤ := ne_top_of_le_ne_top (hb.measure_lt_top.ne) (measure_mono hsub)
  have hgT : 0<s := ENNReal.toReal_pos (hT.measure_pos _ ⟨a,hy⟩).ne' hv
  have he (n : ℕ) : s ≤ (g z/r)^n * t := by
    have ht : ∀ (v : X→ℝ), Continuous v → IntegrableOn v b := fun v hv=> hv.continuousOn.integrableOn_compact hb
    have ht' : ∀ (v : X→ℝ), Continuous v → IntegrableOn v T := fun v hv=> (ht v hv).mono_set hsub
    have hm : s*r^n ≤ t*(g z)^n := by
      calc s*r^n = ∫ _x : X in T,r^n := (setIntegral_const ..).symm
           _ ≤ ∫ x in T,f x^n := setIntegral_mono_on (ht' _ continuous_const) (ht' _ (hf.pow n)) hT.measurableSet fun x hx=>by gcongr; exact hx.1.le
           _ ≤ ∫ x in b,f x^n := setIntegral_mono_set (ht _ (hf.pow _)) ((ae_restrict_mem isClosed_closedBall.measurableSet).mono fun x hx=> pow_nonneg (hp x hx) _) (Eventually.of_forall hsub)
           _ = ∫ x in b,g x^n := hk _
           _ ≤ ∫ _x : X in b,g z^n := setIntegral_mono_on (ht _ (hg.pow _)) (ht _ continuous_const) hb.isClosed.measurableSet fun x hx=>pow_le_pow_left₀ (hQ x hx).1 (hZ hx) _
           _ = _ := setIntegral_const ..
    rw [div_pow,div_mul_eq_mul_div,le_div_iff₀ (by positivity)]; linarith
  have hx := ge_of_tendsto' ((tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hr'.le) ((div_lt_one hr').mpr hr)).mul_const t) he
  linarith

theorem interview {A B : Track I N} (h : Seen A B) (hA : ∀ i,Continuous (A i)) (hB : ∀ i,Continuous (B i))
    {a : X} (ha : a∈ ball 0 1) : ∃ b∈K,∀ i:N, A i a=B i b := by
  classical
  let S (i : N) := {x:X|B i x=A i a}
  have he : IsCompact K:=isCompact_closedBall ..
  suffices H : (K ∩ ⋂ i : N,S i).Nonempty by
    obtain ⟨b,hb,hs⟩:=H; exact ⟨b,hb,fun i=> Eq.symm ((mem_iInter.mp hs) i)⟩
  apply he.inter_iInter_nonempty S (fun i=>isClosed_eq (hB i) continuous_const)
  intro s
  by_contra! hT
  let P (i:N) : Fold I := (A i,B i)-(A i a) • 1
  have hP (i:N) : P i∈ shelf A B:= Submodule.sub_mem _ (symbols A B _) (Submodule.smul_mem _ _ (sits_one A B))
  let T : Fold I := ∑ i∈s,(P i)^2
  have ht : T∈shelf A B:=Submodule.sum_mem _ (fun i _=> sits_power (hP i) _)
  have hi:=seen_on h hA hB ht
  let Δ (F : Track I N) (y : X) := ∑ i∈s, (F i y-A i a)^2
  have h1 (y:X) : T.1 y= Δ A y := by simp [Δ,T,P,Prod.fst_sum,Finset.sum_apply]
  have h2 (y:X) : T.2 y= Δ B y := by simp [Δ,T,P,Prod.snd_sum,Finset.sum_apply]
  have h3 (y : X) (hy:y∈ K) : 0 < T.2 y := by
    rw [h2]; unfold Δ
    apply Finset.sum_pos' (fun _ _=> sq_nonneg _)
    by_contra! hq
    have hz (i) (hi:i∈s) : y∈S i:= by
      specialize hq i hi; change _=_; nlinarith [sq_nonneg (B i y-A i a)]
    have hw : y ∈ K∩⋂ i∈s,S i:=⟨hy,mem_iInter.mpr fun i=>mem_iInter.mpr fun H=> hz _ H⟩
    rw [hT] at hw; exact hw
  have hn : Set.Nonempty K:=⟨a,ball_subset_closedBall ha⟩
  obtain ⟨p,hp,hP⟩:= he.exists_isMaxOn hn hi.1.continuousOn
  obtain ⟨q,hq,hQ⟩:= he.exists_isMaxOn hn hi.2.1.continuousOn
  let d := max (T.1 p) (T.2 q)+1
  let R := d • (1:Fold I)-T
  refine noPeak (f:=R.1) (g:=R.2) (C:=d) ?_ ?_ ha ?_ (fun x hx=> ?_) (fun x hx=>?_ ) (fun n=>?_ )
  · exact (continuous_const.mul continuous_const).sub hi.1
  · exact (continuous_const.mul continuous_const).sub hi.2.1
  · change d*1-T.1 a=_; simp [h1,Δ]
  · change 0 ≤ d*1-T.1 x; have : T.1 x ≤ T.1 p:= hP hx; unfold d; linarith [le_max_left (T.1 p) (T.2 q)]
  · change 0 ≤ d*1-T.2 x ∧ d*1-T.2 x<d; have : T.2 x ≤ T.2 q:= hQ hx; unfold d; obtain ht:= h3 x hx; constructor <;> linarith [le_max_right (T.1 p) (T.2 q)]
  have hr := sits_power ((shelf A B).sub_mem (show d • (1:Fold I)∈ shelf A B from Submodule.smul_mem _ _ (sits_one A B)) ht) n
  have hu : (∫ x in K,(R^n).1 x)=∫ x in K,(R^n).2 x := (seen_on h hA hB hr).2.2
  simpa [Pi.pow_apply] using hu

end YM.RG11.Rigidity.Prism
