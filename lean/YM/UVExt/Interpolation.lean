import YM.Extraction.Lipschitz

/-!
# Multilinear grid interpolants

For an array on covering positions (typically periodic), interpolate on the closed
unit-cell coordinates at physical pitch. Distinguish values only; subsequent derivative
claims interpolate the normalized lattice difference arrays, not classical derivatives of
this multilinear object at seams.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Grid
open Set Filter Function Extraction Lattice
open scoped BigOperators Topology Classical

abbrev Args (n : ℕ) := Fin n → Cover
abbrev Index (n : ℕ) := Fin n × Axis
abbrev Corners (n : ℕ) := Index n → Bool
variable {n : ℕ}

def pos (u : Args n) (s : Corners n) : Args n := fun i a=>if s (i,a) then u i a else u i a - 1

def bary (t : ℝ) (u : Args n) (x : Points n) (p : Index n) (c : Bool) :=
  let k := x p.1 p.2 / t - (u p.1 p.2 : ℝ) + 1
  if c then k else 1-k

def mass (t : ℝ) (u : Args n) (x : Points n) (s : Corners n) := ∏ i, bary t u x i (s i)

def inCube (t : ℝ) (u : Args n) (x : Points n) := ∀ i a,
   t*((u i a-1:ℤ):ℝ) ≤ x i a ∧ x i a ≤ t*(u i a : ℝ)
lemma address_cube {t : ℝ} (ht : 0<t) (x : Points n) : inCube t (address t x) x := by
  intro i a
  obtain ⟨h,k⟩ := (tile_bounds ht (x i a) _).mp (show _ = address t x i a from rfl)
  exact ⟨(by push_cast; exact h.le),k⟩ -- tiles use real subtraction
lemma mass_nonneg {t : ℝ} {x : Points n} {u : Args n} (hw : inCube t u x) (ht : 0<t) (s : Corners n) : 0 ≤ mass t u x s := by
  apply Finset.prod_nonneg; rintro ⟨i,a⟩ _
  have h := hw i a; push_cast at h
  unfold bary
  simp only
  have hx := (le_div_iff₀ ht).mpr (by simpa [mul_comm] using h.1)
  have hy := (div_le_iff₀ ht).mpr (by simpa [mul_comm] using h.2)
  split_ifs <;> linarith
@[simp] lemma sum_mass (t : ℝ) (u : Args n) (x : Points n) : ∑ s, mass t u x s = 1 := by
  unfold mass; rw [← Fintype.prod_sum]; 
  apply Finset.prod_eq_one; intro i hi; simp [bary]; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def blend (t : ℝ) (u : Args n) (f : Args n → E) (x : Points n) := ∑ s, mass t u x s • f (pos u s)
def interpolate (t : ℝ) (f : Args n→E) (x : Points n) := blend t (address t x) f x
theorem at_tag {t : ℝ} (ht : 0<t) (b : Args n) (f : Args n→E) : interpolate t f (tag t b) = f b := by
  unfold interpolate; rw [address_matched ht]
  unfold blend; rw [Finset.sum_eq_single_of_mem (by exact fun _=>true : Corners n) (Finset.mem_univ _)]
  · rw [show pos b (fun _=>true)=b from rfl]; simp [mass,bary, tag,mul_div_cancel_left₀ _ ht.ne',points]
  intro c _ hc
  obtain ⟨p,hp⟩ := not_forall.mp (show ¬ ∀ i,c i = true from mt funext hc)
  unfold mass; rw [Finset.prod_eq_zero (Finset.mem_univ p),zero_smul]
  simp [bary,hp,tag,points,mul_div_cancel_left₀ _ ht.ne']

/-!
To pass boundary values, the affine formulas coincide on the intersections of **closed** cubes.
-/
private def toggle (u v : Args n) : Corners n ≃ Corners n where
  toFun := fun s p => if u p.1 p.2 = v p.1 p.2 then s p else !(s p)
  invFun := fun s p => if u p.1 p.2 = v p.1 p.2 then s p else !(s p)
  left_inv s := funext fun p=>by by_cases h : u p.1 p.2 = v p.1 p.2 <;> simp [h]
  right_inv s := funext fun p=>by by_cases h : u p.1 p.2 = v p.1 p.2 <;> simp [h]

private lemma swap_eq {t : ℝ} (ht : 0<t) {u v : Args n} {x : Points n} (hu : inCube t u x) (hv : inCube t v x)
    (s : Corners n) : mass t u x s = mass t v x (toggle u v s) ∧ (mass t u x s=0 ∨ pos u s=pos v (toggle u v s)) := by
  have h (i:Index n) : bary t u x i (s i) = bary t v x i ((toggle u v s) i) ∧
      (bary t u x i (s i)=0 ∨ pos u s i.1 i.2=pos v (toggle u v s) i.1 i.2) := by
    by_cases hn : u i.1 i.2=v i.1 i.2
    · simp [bary,pos,toggle,hn]
    have h := hu i.1 i.2
    have h' := hv i.1 i.2
    have hsep (a b : ℤ) (ha : a < b) (hi : t*(b:ℝ)-t ≤ x i.1 i.2) (hj : x i.1 i.2 ≤ t*(a:ℝ)) : b=a+1 ∧ x i.1 i.2/t=a := by
      have h₀ : (a:ℝ)+1 ≤ b := by exact_mod_cast ha
      have h₁ : b=a+1 := le_antisymm (by exact_mod_cast (show (b:ℝ) ≤ a+1 by nlinarith)) ha
      push_cast at hi hj; rw [h₁] at hi; push_cast at hi
      exact ⟨h₁,(div_eq_iff ht.ne').mpr (by nlinarith)⟩
    push_cast at h h'
    rcases lt_or_gt_of_ne hn with hc|hc
    · obtain ⟨ha,hb⟩ := hsep (u i.1 i.2) (v i.1 i.2) hc (by linarith) h.2
      cases hi : s i <;> simp [bary,pos,toggle, *]
    · obtain ⟨ha,hb⟩ := hsep (v i.1 i.2) (u i.1 i.2) hc (by linarith) h'.2
      cases hi : s i <;> simp [bary,pos,toggle, *]
  refine ⟨Finset.prod_congr rfl (fun i _=>(h i).1),?_⟩
  exact Classical.or_iff_not_imp_left.mpr (fun hw=> funext fun i => funext fun a =>
    ((h (i,a)).2.resolve_left (fun he=> hw (Finset.prod_eq_zero (Finset.mem_univ (i,a)) he))))

lemma overlap (t : ℝ) (ht : 0<t) {u v : Args n} {x : Points n} (hu : inCube t u x) (hv : inCube t v x)
    (f : Args n→E) : blend t u f x = blend t v f x := by
  refine Fintype.sum_equiv (toggle u v) _ _ fun s=> ?_
  obtain ⟨h,he|he⟩ := swap_eq ht hu hv s
  · simp [← h,he]
  rw [h,he]

private lemma blend_continuous (t : ℝ) (u : Args n) (f : Args n→E) : Continuous (blend t u f) := by
  refine continuous_finsetSum _ (fun i _=> Continuous.smul (continuous_finsetProd _ (fun a _ => ?_)) continuous_const)
  unfold bary; dsimp; split_ifs <;> fun_prop

theorem continuous (t : ℝ) (ht : 0<t) (f : Args n → E) : Continuous (interpolate t f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let W:= Finset.image (fun c=>pos (address t x + fun _ _=>1) c) Finset.univ
  have memW : ∀ᶠ y in 𝓝 x, address t y ∈ W := by
    let a:=address t x
    have h (i:Index n) : ∀ᶠ y in 𝓝 x, address t y i.1 i.2 = a i.1 i.2 ∨ address t y i.1 i.2 = a i.1 i.2+1 := by
      obtain ⟨l,h⟩ := (tile_bounds ht (x i.1 i.2) _).1 (show _ = a i.1 i.2 from rfl)
      filter_upwards [(show Continuous fun y:Points n=> y i.1 i.2 by fun_prop).continuousAt.preimage_mem_nhds
        (show Ioo _ _ ∈ 𝓝 (x i.1 i.2) from Ioo_mem_nhds l (by linarith : x i.1 i.2 < t*((a i.1 i.2 : ℝ)+1)))] with y hy
      obtain ⟨hy₀,hy₁⟩ := (Set.mem_preimage.mp hy : _ ∧ _)
      by_cases hv : y i.1 i.2 ≤ t*(a i.1 i.2 : ℝ)
      · exact Or.inl ((tile_bounds ht _ _).2 ⟨hy₀,hv⟩)
      push Not at hv
      exact Or.inr ((tile_bounds ht _ _).2 (by unfold tile; simpa [(by ring : (t:ℝ)*((a i.1 i.2+1:ℝ)-1)=t*a i.1 i.2)] using And.intro hv hy₁.le))
    filter_upwards [eventually_all.mpr h] with y hy
    refine Finset.mem_image.mpr ⟨fun p=>decide (address t y p.1 p.2≠a p.1 p.2),Finset.mem_univ _,funext fun i=>funext fun b=>?_⟩
    rcases hy (i,b) with h|h <;> simp_all [pos,a]
  let Q:= W.filter (fun u=>inCube t u x)
  have memQ : ∀ᶠ y in 𝓝 x, address t y ∈ Q := by
    have h (u) : IsClosed {y:Points n | inCube t u y} := by
      simp [inCube]
      convert isClosed_biInter (s:=(Set.univ : Set (Index n))) (f:=fun p=>{z:Points n | t*((u p.1 p.2-1:ℤ):ℝ) ≤ z p.1 p.2 ∧ z p.1 p.2 ≤ t*(u p.1 p.2:ℝ)}) (fun p _=> by
        exact IsClosed.inter (isClosed_le (f:=(fun _ : Points n=>_)) (g:=fun y=> y p.1 p.2) continuous_const (by fun_prop)) (isClosed_le (f:=(fun y : Points n=> y p.1 p.2)) (g:=fun _=>_) (by fun_prop) continuous_const)) using 1
      ext y; simp
    have hi (u) : ∀ᶠ z in 𝓝 x, inCube t u z → inCube t u x := by
      by_cases hl : inCube t u x
      · exact .of_forall fun _ _=>hl
      refine (Filter.Eventually.mono (p:=fun y=>y∈ {z:Points n | inCube t u z}ᶜ) (hp:=((h u).isOpen_compl.mem_nhds hl)) ?_)
      exact fun _ hv hP=> (hv hP).elim
    filter_upwards [memW,(eventually_all_finset W).mpr fun i _ => hi i] with y hy hu
    exact Finset.mem_filter.mpr ⟨hy,hu _ hy (address_cube ht y)⟩
  refine Filter.tendsto_def.mpr fun U hU => ?_
  have h (i) (hi:i ∈ Q) : ∀ᶠ y in 𝓝 x, blend t i f y ∈ U := by
    refine (blend_continuous t i f|>.continuousAt).eventually ?_
    rw [overlap t ht (Finset.mem_filter.mp hi).2 (address_cube ht x)]; exact hU
  filter_upwards [memQ,(eventually_all_finset Q).mpr h] with y hy hp
  exact hp _ hy

/-- Every period vector on the covering grid is respected. -/
theorem periodic (t : ℝ) (ht : 0<t) (a : Args n) (f : Args n→E) (H : ∀ u, f (u+a)=f u) (x : Points n) :
    interpolate t f (x + tag t a) = interpolate t f x := by
  have h (p : Index n) : address t (x+tag t a) p.1 p.2= address t x p.1 p.2 + a p.1 p.2 := by
    change ⌈(x p.1 p.2+t*a p.1 p.2)/t⌉= _; rw [add_div,mul_comm t,mul_div_cancel_right₀ _ ht.ne',Int.ceil_add_intCast]; rfl
  refine Finset.sum_congr rfl fun s _=> ?_
  rw [show pos (address t (x+tag t a)) s=(pos (address t x) s + a) from funext fun i=>funext fun b=>by
     simp [pos,h (i,b)]; split_ifs <;> ring,H]
  congr 1; apply Finset.prod_congr rfl; intro p _
  simp only [bary,h,Int.cast_add,PiLp.add_apply]
  unfold tag
  dsimp [points]
  split_ifs <;> rw [add_div,mul_comm t,mul_div_cancel_right₀ _ ht.ne'] <;> ring

theorem bound_dist (t : ℝ) (ht : 0<t) (x : Points n) (c : E) (f : Args n→E) {R : ℝ}
    (hf : ∀ s, dist (f (pos (address t x) s)) c ≤ R) :
    dist (interpolate t f x) c ≤ R := by
  let w:= mass t (address t x) x
  let ξ (s) := pos (address t x) s
  have h (s) : ‖w s‖ = w s := Real.norm_of_nonneg (mass_nonneg (address_cube ht x) ht s)
  change dist (∑ s, w s • f (ξ s)) c ≤ R
  rw [dist_eq_norm]
  conv_lhs => rw [show c=(1:ℝ) • c from (one_smul ℝ c).symm]; rw (occs:=[1]) [← sum_mass t (address t x) x]
  change ‖(∑ s, w s • f (ξ s)) - (∑ s, w s) • c‖ ≤ _
  rw [Finset.sum_smul,← Finset.sum_sub_distrib]; simp_rw [← smul_sub]
  calc
    _ ≤ ∑ s, w s * dist (f (ξ s)) c := (norm_sum_le ..).trans_eq (Finset.sum_congr rfl (fun i _ => by rw [dist_eq_norm,norm_smul,h]))
    _ ≤ ∑ s, w s * R := Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_left (hf _) (h i ▸ norm_nonneg _ : 0≤w i)
    _ = R := by rw [← Finset.sum_mul, (sum_mass t (address t x) x : ∑ i, w i=1),one_mul]

theorem corner_dist {t : ℝ} (ht : 0<t) (x : Points n) (s : Corners n) :
    dist (tag t (pos (address t x) s)) x ≤ (4*n : ℝ)*t := by
  apply (sq_le_sq₀ dist_nonneg (by positivity)).1
  rw [dist_eq_norm, ← Points.flatten.norm_map, EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ i:Index n, t^2 := Finset.sum_le_sum (fun i _=>sq_le_sq.mpr ?_)
    _ ≤ _ := ?_
  · change |(t*((pos (address t x) s i.1 i.2:ℤ):ℝ)-x i.1 i.2)|≤ _
    rw [abs_of_nonneg ht.le, abs_le]; obtain ⟨a,b⟩ := address_cube ht x i.1 i.2
    unfold pos; split_ifs <;> push_cast at * <;> constructor <;> linarith
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  cases n with
  | zero => norm_num
  | succ n =>
    have h : (4*((n+1:ℕ):ℝ) : ℝ) ≤ (4*((n+1:ℕ):ℝ))^2 := by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right ((mul_comm ..).le.trans h) (sq_nonneg _)
end YM.UVExt.Grid
