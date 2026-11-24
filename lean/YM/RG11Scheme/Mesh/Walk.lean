import YM.RG11Scheme.Mesh.Bands

/-! Limit budgets and exact on-shell harmonicity away from the source. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Mesh
open Lattice Function Filter Set Pert Align Full Cellular Next.Rank.Radian
open scoped Topology BigOperators Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (T:Itinerary)
def flat (x : ℕ→E) : Prop := ∀ d:ℕ,Tendsto (fun i=> ((T.gap i)^d)⁻¹ • x i) atTop (𝓝 0)
def near (x:ℕ→Cover) := ∃ d:ℕ, ∃ C>0, ∀ᶠ i in atTop, wide (x i)≤ C/(T.gap i)^d
-- name collision Full "visits"
variable {T} {p q:ℕ→Cover}
theorem nears (x:Cover) : near T (fun _=>x) := ⟨0, wide x,wide_pos x, by simp⟩
lemma last_one : ∀ᶠ i in atTop,T.gap i≤1 := T.cutoff.eventually (ge_mem_nhds zero_lt_one)
lemma near.plus (hp : near T p) (hq : near T q) : near T fun i=>p i+q i := by
   obtain ⟨d,U,h,H⟩:=hp; obtain ⟨k,Q,u,J⟩:=hq; refine ⟨d+k,U+Q,by positivity,?_⟩
   filter_upwards [H,J,last_one (T:=T)] with i hi hi' he; have hp:=T.positive i
   apply (wide_plus _ _).trans; rw [add_div]; apply add_le_add (hi.trans ?_) (hi'.trans ?_)
   · exact div_le_div_of_nonneg_left h.le (by positivity) (by rw [pow_add]; exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hp.le he))
   exact div_le_div_of_nonneg_left u.le (by positivity) (by rw [pow_add]; exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hp.le he))
lemma near.minus (hp:near T p) : near T fun i=> -p i := by simpa only [near,wide_neg] using hp
lemma local_arc {x:E4} (h:Tendsto (fun i=> Full.incVec (T.gap i) (p i)) atTop (𝓝 x)) : near T p := by
   have he:Tendsto (fun i=> T.gap i * ‖row (p i)‖ + T.gap i) atTop (𝓝 ‖x‖):= by simpa only [inc_row,norm_smul,Real.norm_of_nonneg (T.positive _).le, add_zero] using h.norm.add T.cutoff
   refine ⟨1,‖x‖+1,by positivity,?_⟩
   filter_upwards [he.eventually (ge_mem_nhds (lt_add_one _))] with i hi; rw [pow_one]; apply (le_div_iff₀ (T.positive i)).mpr; apply le_trans _ hi
   unfold wide; nlinarith only [elev_min (p i),T.positive i]
lemma near.unwrap (h:near T p) : ∀ᶠ i in atTop,lift (wrap (T.period i) (p i))=p i := by
   obtain ⟨d,W,h,U⟩:=h
   filter_upwards [U,(T.huge d).eventually (eventually_gt_atTop (2*W))] with i hi hu
   refine lift_eq_iff.mpr ⟨rfl,fun k=>?_⟩
   apply And.imp (fun x=>(by exact_mod_cast x)) (fun x=>(by exact_mod_cast x)) (_ : -(↑(T.period i).val:ℝ) < 2*(p i k:ℝ) ∧ 2*(p i k:ℝ)≤ ↑(T.period i).val)
   have he := abs_le.mp ((big k (p i)).trans hi)
   have hy : 2*(W/(T.gap i)^d) < ↑(T.period i).val := by rw [←mul_div_assoc]; exact (div_lt_iff₀ (pow_pos (T.positive i) _)).mpr hu
   constructor <;> linarith only [he.1, he.2,hy]
lemma cover_control (h:near T p) : flat T (fun i=> field (wrap (T.period i) (p i))-coverLine (p i)) := by
   obtain ⟨d,B,hB,hP⟩:=h
   obtain ⟨C,hC,A,hA,U⟩:=clearing
   intro k; rw [tendsto_zero_iff_norm_tendsto_zero]
   let X (i:ℕ) := (T.gap i)^k
   let q := d+k+4*(k+1)
   let L (i:ℕ) := C*(T.gap i)^(k+2)+A*B*(((T.period i).val:ℝ)*(T.gap i)^q)⁻¹
   have he : Tendsto L atTop (𝓝 0):= by
       simpa only [Function.comp_apply,mul_zero,zero_pow (show k+2≠0 by omega), mul_zero, add_zero] using (((T.cutoff.pow (k+2)).const_mul C).add ((tendsto_inv_atTop_zero.comp (T.huge q)).const_mul (A*B)))
   apply squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) _ he
   filter_upwards [hP,last_one (T:=T), (T.huge (k+1)).eventually (eventually_ge_atTop 8)] with i hi hx hh
   have hp := T.positive i
   let r := (T.gap i)^(k+1)
   have hb : 8*((T.period i).val:ℝ)⁻¹ ≤ r := (div_le_iff₀ (Full.val_pos _)).mpr (by simpa only [r,mul_comm (T.gap i ^ (k+1))] using hh)
   rw [norm_smul,Real.norm_of_nonneg (by positivity)]
   grw [U (T.even_at i) (pow_pos (T.positive i) _) (pow_le_one₀ hp.le hx) hb, hi]
   apply le_of_eq
   unfold L q; have h':=Full.val_pos (T.period i); rw [pow_add _ _ (4*(k+1)), Nat.mul_comm 4, pow_mul, pow_add _ d, pow_succ, pow_add _ k]
   field_simp; ring
lemma flat_sub {p q:ℕ→E} (h:flat T p)(hh:flat T q) : flat T fun i=>p i-q i:= fun i=>by simpa only [smul_sub,sub_zero] using (h i).sub (hh i)
lemma differs (D : List Axis) (hp:near T p) : flat T fun i=> go D field (wrap (T.period i) (p i))-go D coverLine (p i) := by
   induction D generalizing p with
   | nil=> exact cover_control hp
   | cons i D IH =>
      have he:= flat_sub (T:=T) (E:=ℝ) (IH (hp.plus (nears (step i)))) (IH hp)
      unfold flat at *; simp only [map_add,wrap_step] at he
      intro k; convert! he k using 2; simp only [onwards]; congr 1; abel
lemma flat_zero {x : ℕ→E} (h:flat T x): Tendsto x atTop (𝓝 0) := by simpa only [pow_zero,inv_one,one_smul] using h 0
lemma cover_measured (D : List Axis) {z:E4} (hz:z≠0) (hc:Tendsto (fun i=>Full.incVec (T.gap i) (p i)) atTop (𝓝 z)) : Tendsto (fun i=>((T.gap i)^(D.length+2))⁻¹ * go D coverLine (p i)) atTop (𝓝 (Band.casual D z).re) := by
   let s (i:ℕ) := wrap (T.period i) (p i)
   have hL := local_arc hc
   have he:= Band.joint_casual _ _ _ D s hz T.grid_eq T.positive T.clears T.cutoff (hc.congr' ((near.unwrap hL).mono fun i hi=> by dsimp only [s]; rw [hi]))
   have ht:= (Complex.reCLM.continuous.tendsto (Band.casual D z)).comp he
   simp only [Function.comp_def, Complex.reCLM_apply, ←torus_joint] at ht
   simpa only [smul_eq_mul,Lattice.wrap_step,s,mul_sub, sub_sub_cancel, sub_zero] using ht.sub (differs D hL (D.length+2))

private def chain := itinerary 2 (by simp)
lemma cover_bound (D) : ∃ C>0,∀ x, ‖go D coverLine x‖ ≤ C/wide x^(D.length+2) := by
   obtain ⟨C,hC,H⟩:=lift_bound D
   refine ⟨C,hC,fun x=>?_⟩
   let u i := go D field (wrap (chain.period i) x)
   have he : Tendsto u atTop (𝓝 (go D coverLine x)) := by simpa only [sub_add_cancel, zero_add] using (flat_zero (E:=ℝ) (T:=chain) (differs D (nears x))).add_const (go D coverLine x)
   exact le_of_tendsto he.norm ((placement x chain).mono fun i hi=> hi ▸ H (chain.period i) (chain.even_at i) _)
lemma recovery (x:Cover) : Tendsto (fun m=> field (wrap (T.period m) x)) atTop (𝓝 (coverLine x)) := by
   simpa only [sub_add_cancel,zero_add] using (flat_zero (cover_control (nears (T:=T) x))).add_const (coverLine x)
@[simp] lemma opposite (x:Cover) : coverLine (-x) = coverLine x := by
   apply tendsto_nhds_unique (recovery (T:=chain) (-x)); simpa only [field, map_neg,toroid_even] using (show Tendsto (fun m=> field (-wrap (chain.period m) x)) atTop (𝓝 (coverLine x)) from (recovery _).congr (fun _=>(toroid_even ..).symm))
lemma laplace (x:Cover) : ∑ i:Axis,(coverLine (x+step i)+coverLine (x-step i)-2 * coverLine x) = -(if x=0 then 1 else 0) := by
   let K (m:ℕ) (y:Cover) := field (wrap (chain.period m) y)
   let q (m:ℕ) := ((chain.period m).val:ℝ)^(-4:ℤ)
   have h : Tendsto (fun m=>∑ i:Axis,(K m (x+step i)+K m (x-step i)-2*K m x)) atTop (𝓝 _) := tendsto_finsetSum _ (fun i _=>((recovery (T:=chain) (x+step i)).add (recovery (x-step i))).sub ((recovery x).const_mul 2))
   have ht : Tendsto q atTop (𝓝 0) := by
       have he : Tendsto (fun i=> ((chain.period i).val:ℝ)) atTop atTop := by simpa only [pow_zero,mul_one] using chain.huge 0
       unfold q; simp_rw [zpow_neg,show ∀ a:ℝ, a^(4:ℤ) = a^4 from fun a=> zpow_natCast ..]; exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : (4:ℕ) ≠0)).comp he)
   apply tendsto_nhds_unique h
   simp_rw [K]; have hp := placement x chain
   rw [← add_zero (-_)]
   apply ((tendsto_const_nhds (x:=-(if x=0 then (1:ℝ) else 0))).add ht).congr'
   filter_upwards [hp] with i hi
   simp_rw [map_add,map_sub,wrap_step]
   have he : wrap (chain.period i) x=0 ↔ x=0 := ⟨fun e=> hi.symm.trans ((congr_arg lift e).trans (by ext; simp [lift])), fun e=>by rw [e,map_zero]⟩
   have hl := Full.lap_eq (wrap (chain.period i) x); apply Eq.symm; have hr:=congrArg Complex.re hl
   change ∑ z:Axis, ((toroid _).re+ (toroid _).re- 2* (toroid _).re) = _
   simp only [he] at hr
   split_ifs <;> rename_i hu <;> simp only [hu, if_true,if_false, Complex.neg_re, Complex.add_re,Complex.sub_re,Complex.re_sum,← Complex.ofReal_natCast,← Complex.ofReal_zpow, Complex.ofReal_re,two_smul, Complex.one_re, Complex.zero_re, two_mul] at hr ⊢ <;> exact hr
end YM.RG11Scheme.Mesh
