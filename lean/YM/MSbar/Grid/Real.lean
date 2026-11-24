import YM.MSbar.Grid.Euclid

/-! Width examples for the Ward port. Staging costs don't depend on lattice cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Set MeasureTheory Metric Filter Dim
open scoped Topology BigOperators Classical ENNReal
namespace Snap
lemma supported : Nonempty (Snap ℝ volume):=by
   let t (n:ℕ):ℝ:=n+1
   let f (n:ℕ): ℤ →+ ℝ:= ⟨⟨fun x=> x/t n,by simp⟩,fun x y=> by push_cast; ring⟩
   let g n (x:ℝ):= f n (Int.floor (x*t n)); let K (n:ℕ):ℤ:= (n+1)^2;let U (n):=(Finset.Icc (-(K n)) (K n)).image (f n)
   have hp(n):0<t n:= by unfold t; positivity
   have hT(n): (K n:ℝ)=t n^2:=by simp [t,K]
   have hi(n):Injective (f n):=by
      intro x y h; change (x:ℝ)/t n=y/t n at h;exact_mod_cast (div_left_inj' (hp n).ne'|>.mp h)
   have hv n i:g n ⁻¹' {f n i}=Ico (i/t n) ((i+1:ℤ)/t n):= by
      ext x; change f n (Int.floor _)=_ ↔ _ ≤ _ ∧ _ < _; rw [(hi n).eq_iff,Int.floor_eq_iff,div_le_iff₀ (hp n),lt_div_iff₀ (hp n)]; push_cast;rfl
   have he(n) (x:ℝ): dist (g n x) x≤ (t n)⁻¹:=by
      let i:=Int.floor (x*t n); have h : x∈ Ico (i/t n) ((i+1:ℤ)/t n):= hv n i ▸ (show g n x=f n i from rfl)
      change dist (i/t n) x≤_; rw [Real.dist_eq,abs_le]; obtain ⟨hr,hh⟩:=h; push_cast at hh; rw [add_div,one_div] at hh; constructor <;> linarith [show 0<(t n)⁻¹ from inv_pos.mpr (hp _)]
   refine ⟨⟨fun n=>(f n).range,U,fun n=>(t n)⁻¹,fun n=>(inv_pos.mpr (hp n)).le,g,fun n x=>⟨_,rfl⟩,fun n x hx=>by obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx; exact ⟨_,rfl⟩,?_,?_,fun n x hx=>?_,fun n x hx=>?_,fun x=>?_⟩⟩
   · intro H h; obtain ⟨b,hb⟩:= h.exists_bound_of_continuousOn continuous_id.continuousOn
     have h : Tendsto t atTop atTop:= tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
     filter_upwards [h.eventually_ge_atTop b] with n ht x hx; obtain ⟨i,hi⟩:=hx.2; subst x; refine Finset.mem_image.mpr ⟨i,Finset.mem_Icc.mpr ?_,rfl⟩
     have hh: |(i:ℝ)/t n|≤t n:=(hb _ hx.1).trans ht; obtain ⟨hL,hR⟩:=abs_le.mp hh; constructor
     · exact_mod_cast (show -(K n:ℝ) ≤ i by rw [hT]; nlinarith only [(le_div_iff₀ (hp n)).mp hL])
     exact_mod_cast (show (i:ℝ)≤ K n by rw [hT]; nlinarith only [(div_le_iff₀ (hp n)).mp hR])
   · intro K h; obtain ⟨b,hb⟩:= h.exists_bound_of_continuousOn continuous_id.continuousOn
     refine ⟨closedBall 0 (b+1), isCompact_closedBall ..,Eventually.of_forall (fun n x hx=> mem_closedBall_zero_iff.mpr ?_)⟩;rw [← dist_zero_right x]; exact (dist_triangle x (g n x) _).trans (by rw [dist_zero_right, add_comm b, dist_comm x]; exact add_le_add ((he ..).trans (inv_le_one_of_one_le₀ (by unfold t; simp))) (hb _ hx))
   · obtain ⟨i,hi,rfl⟩:= Finset.mem_image.mp hx; rw [hv]; exact measurableSet_Ico
   · obtain ⟨i,hi,rfl⟩:= Finset.mem_image.mp hx; rw [hv,Real.volume_Ico]; congr 1; push_cast; ring
   rw [Metric.tendsto_nhds]; intro ε hε; exact (((tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop (R:=ℝ)) : Tendsto t atTop atTop))).eventually (gt_mem_nhds hε)).mono fun n hn=> (he n x).trans_lt hn
end Snap
end YM.MSbar.Loops
