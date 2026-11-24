import YM.SchemeConversionRG11.FirstW.Ship.Wings
/-! Site-rooted estimates for integral cubic mixed image lines. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T : Itinerary} {G : Gauge}
def Splines (T : Itinerary) (x : StepPath T) (A : Sight T G) : Prop := ∀ q:Cover,∀ b:Axis, ∃ C>0,∀ᶠ i in atTop,∀ z : Site (T.period i), ‖A i (z+wrap _ q,b)‖≤C*lag (z-x i)
lemma flex (T : Itinerary) (v : Cover) : ∃ C:ℝ,0<C ∧ ∀ᶠ i in atTop,∀ x:Site (T.period i),lag (x+wrap (T.period i) v)≤C*lag x := by
  let b:= (1+stepY v)
  have hb : 0<b := by unfold b; linarith [unit_stepY v];
  refine ⟨b^3,pow_pos hb _,?_⟩
  refine (past T v).mono fun i hi x=> ?_
  unfold lag; have hC:= unit_cy (x+wrap (T.period i) v)
  have ht:= unit_cy x
  rw [inv_le_comm₀]; rotate_left
  · positivity
  · positivity
  rw [mul_inv,inv_inv,inv_mul_le_iff₀ (pow_pos hb _),←mul_pow]; exact pow_le_pow_left₀ (zero_le_one.trans ht) (hi x).2 3
lemma canal_base (T : Itinerary) (k : Labels.Key G) (o : StepPath T) : Splines T o (fun i=>canal k (o i)) := by
  intro v b
  obtain ⟨D,hD,H⟩:=tread k T b []; obtain ⟨C,hC,E⟩:=flex T v
  refine ⟨D*C,mul_pos hD hC,?_⟩; filter_upwards [E,H] with i hi ht x
  let l := x+wrap _ v-o i
  have hx : l=x-o i+wrap _ v := by unfold l; abel
  have h:=ht (x+wrap _ v) (o i); let r:=‖canal k (o i) (x+wrap (T.period i) v,b)‖
  have h1 := unit_cy l; change (cy l)^(0+mass k+1)*r≤D at h
  have hh := pow_le_pow_right₀ h1 (show 3≤0+mass k+1 by unfold mass; omega)
  have hh := (mul_le_mul_of_nonneg_right hh (show 0≤r from norm_nonneg _)).trans h
  have hr : r ≤ D*lag l := (le_div_iff₀ (pow_pos (zero_lt_one.trans_le h1) _)).2 (by rwa [mul_comm]);
  exact hr.trans (by rw [hx,mul_assoc]; gcongr; exact hi _)
variable {o : StepPath T} {A B C : Sight T G}
lemma spline_image (h : Splines T o A) : Splines T (-o) (fun i=>reflectT G (T.period i) (A i)) := by
  intro p b
  obtain ⟨D,hD,H⟩:=h (-p-step b) b
  refine ⟨D,hD,H.mono fun i hi x=>?_⟩
  dsimp only; rw [show reflectT G _ (A i) (x+wrap (T.period i) p,b) = -A i (-x+wrap _ (-p-step b),b) by simp [reflectT,Orb.image]; congr 3; abel, norm_neg];
  exact (hi (-x)).trans (le_of_eq (by rw [show -x - o i = -(x - (-o) i) from by simp; abel, lag,cy_neg];rfl))
private lemma capstone {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] (K:N→ₗ[ℝ] N→ₗ[ℝ] N→ₗ[ℝ] ℝ) : ∃ C>0, ∀ x y z, ‖K x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖ := by
  let b:=Module.finBasis ℝ N
  let Y (i) : N→L[ℝ] N→L[ℝ] ℝ := ((LinearMap.toContinuousLinearMap : (N→ₗ[ℝ] ℝ)≃ₗ[ℝ](N→L[ℝ] ℝ)).toLinearMap.comp (K (b i))).toContinuousLinearMap
  let J i:= (b.coord i).toContinuousLinearMap
  let R:=∑ i, ‖J i‖*‖Y i‖
  have hp: 0≤R:=Finset.sum_nonneg fun i _=>by positivity
  refine ⟨R+1,by linarith,fun x y z=>?_⟩
  have hx : K x y z=∑ i,J i x*Y i y z := by nth_rw 1 [← b.sum_repr x]; simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply];rfl
  rw [hx]; apply (norm_sum_le ..).trans
  refine (Finset.sum_le_sum (g:=fun i=> (‖J i‖ * ‖Y i‖)*(‖x‖*‖y‖*‖z‖)) (fun i _=>?_)).trans ?_
  · rw [norm_mul]
    exact le_trans (mul_le_mul (J i |>.le_opNorm x) (((Y i y).le_opNorm z).trans (mul_le_mul_of_nonneg_right ((Y i).le_opNorm y) (norm_nonneg z))) (norm_nonneg _) (by positivity)) (le_of_eq (by ring))
  rw [←Finset.sum_mul]; change R*_ ≤ _; simp only [mul_assoc]; gcongr; linarith -- maybe auto
lemma lagoon_tri (x y z : StepPath T) (hA : Splines T x A) (hB : Splines T y B) (hC : Splines T z C) (w : Walk) :
    ∃ P>0,∀ᶠ i in atTop,∀ u:Site (T.period i), ‖tower G u w (A i) (B i) (C i)‖≤P*(lag (u-x i)*lag (u-y i)*lag (u-z i)) := by
  obtain ⟨s,he,hV⟩:=finite_ways G 0 w
  let F(A : Sight T G) (i:ℕ) (u : Site (T.period i)) (v:↥s) := A i (u+wrap _ v.val.1,v.val.2)
  have ha (A : Sight T G) i (u : Site (T.period i)): EqOn (terms u (A i)) (cle G s (F A i u)) (s:Set (Edge Cover)) := by intro v hv; dsimp [terms, cle,clearWind,F]; change v∈s at hv; simp [hv,add_comm]
  let L(u v t : s→G.Color) := tower G (0:Cover) w (cle G s u) (cle G s v) (cle G s t)
  have hq (i : ℕ) u : tower G u w (A i) (B i) (C i) = L (F A i u) (F B i u) (F C i u) := by
    have H := tower_wrap (A i) (B i) (C i) u 0 w; simp only [map_zero,zero_add] at H; rw [← H]; unfold L; simp only [tower_eq,spire, LinearMap.add_apply,LinearMap.flip_apply, LinearMap.smul_apply]; rw [he _ _ (ha A i u),he _ _ (ha B i u),he _ _ (ha C i u), hV _ _ _ _ (ha A i u) (ha B i u), hV _ _ _ _ (ha A i u) (ha C i u),hV _ _ _ _ (ha C i u) (ha A i u),hV _ _ _ _ (ha B i u) (ha A i u), hV _ _ _ _ (ha C i u) (ha B i u), hV _ _ _ _ (ha B i u) (ha C i u)]
  have hp' (x : StepPath T)(A : Sight T G)(h : Splines T x A) : ∃ P>0,∀ᶠ i in atTop,∀ u:Site (T.period i), ‖F A i u‖ ≤ P*lag (u-x i) := by
    choose H hP h using fun i:↥s=> h i.val.1 i.val.2; let P:= (1:ℝ)+∑ i:↥s,H i
    have hU : 0<P := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _=>(hP i).le)
    refine ⟨P,hU,(eventually_all.mpr h).mono fun i hi u=>?_⟩
    refine pi_norm_le_iff_of_nonneg (mul_nonneg hU.le (lag_pos _).le) |>.2 (fun v=>?_)
    exact (hi v u).trans (mul_le_mul_of_nonneg_right ((Finset.single_le_sum (fun i _ => (hP i).le) (Finset.mem_univ v)).trans (le_add_of_nonneg_left zero_le_one)) (lag_pos _).le)
  -- promote trilinear over finite-dimensional s to CLMs
  let N:= s→G.Color
  let l : N →ₗ[ℝ] N →ₗ[ℝ] N →ₗ[ℝ] ℝ := {
    toFun u:= ((tower G (0:Cover) w (cle G s u)).compl₂ (cle G s)).comp (cle G s)
    map_add' x y:=LinearMap.ext fun a=>LinearMap.ext fun b=>by simp
    map_smul' c v:=LinearMap.ext fun a=>LinearMap.ext fun b=>by simp }
  obtain ⟨W,hW,Hw⟩:=capstone (N:=s→G.Color) l
  obtain ⟨D,hD,H⟩:=hp' x A hA; obtain ⟨V,hV,E⟩:=hp' y B hB; obtain ⟨J,hJ,Y⟩:=hp' z C hC
  refine ⟨W*D*V*J,by positivity,?_⟩
  filter_upwards [H,E,Y] with i hi hj hk u
  rw [hq]; refine le_trans (Hw (F A i u) (F B i u) (F C i u)) ?_
  grw [hi u, hj u, hk u]
  · ring_nf; exact le_rfl
  all_goals have hx:=lag_pos (u-x i); have hy:=lag_pos (u-y i); have hz:=lag_pos (u-z i); positivity
end YM.RG11.FirstW
