import YM.Pert.Align.Burst
/-! UV line estimates for scheme calibration. Native units, sup torus distance. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SchemeRG11.Catch
open Lattice Function Filter Asymptotics Pert Full Band Cellular Topology
open scoped Classical BigOperators ENNReal
variable {Q E : Type*} [AddCommGroup Q] [One Q] [AddCommGroup E] {n : Side}

abbrev diam (x : Cover) : ℕ := Finset.univ.sup fun i : Axis => (x i).natAbs
lemma diam_lift (z : Site n) : diam (Lattice.lift z)=pdist z := rfl
lemma diam_ge (z : Cover) (i : Axis) : (z i).natAbs ≤ diam z:= Finset.le_sup (s:=Finset.univ) (f:=fun i:Axis=>(z i).natAbs) (Finset.mem_univ i)
lemma diam_add (x y : Cover) : diam (x+y)≤diam x+diam y:= Finset.sup_le (fun i _=> (Int.natAbs_add_le ..).trans (Nat.add_le_add (diam_ge x i) (diam_ge y i)))
@[simp] lemma diam_zero : diam 0 = 0 := by simp [diam]
@[simp] lemma diam_neg (x : Cover) : diam (-x)=diam x:=by simp [diam]
lemma castabs (x : Cover) (i : Axis) : |(x i:ℝ)| ≤ (diam x:ℝ) := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast (diam_ge x i)
lemma chart_ge (x : Cover) : (diam x:ℝ) ≤ ‖incVec 1 x‖ := by
 obtain ⟨i,_,hi⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) Finset.univ_nonempty (fun i:Axis=> (x i).natAbs)
 have hg:= coordinate_le (incVec 1 x) i
 rw [incVec_apply,one_mul,← Int.cast_abs, Int.abs_eq_natAbs,← hi] at hg
 exact_mod_cast hg
lemma chart_le (x : Cover) : ‖incVec 1 x‖ ≤ 2*(diam x:ℝ) := by
 obtain ⟨i,hi⟩:= max_coord (incVec 1 x)
 apply hi.trans (mul_le_mul_of_nonneg_left _ (by norm_num))
 simpa using castabs x i
lemma width (z : Site n) : pdist z ≤ n.val := by
 unfold pdist; apply Finset.sup_le; intro i _; have H:=lift_centers z i; omega
lemma norm_span (a : ℝ) (ha : 0<a) (z : Cover) : ‖incVec a z‖=a*‖incVec 1 z‖ := by rw [← mul_one a, ← to_grid, norm_smul,Real.norm_of_nonneg ha.le,mul_one]

def derive : List Axis → (Four Q→E) → (Four Q→E)
| [],f => f
| j::J,f => fun z => derive J f (z+step j)-derive J f z

lemma derive_period (f : Site n→E) (J : List Axis) (z : Cover) : derive J (f ∘ (wrap n)) z = derive J f (wrap n z):=by
 induction J generalizing z with
 | nil => rfl
 | cons j J ih => simp only [derive]; rw [ih, ih,map_add, wrap_step]
lemma derive_shift (f : Four Q → E) (u : Four Q) (J : List Axis) (z : Four Q) : derive J (fun x=> f (x+u)) z=derive J f (z+u):=by
 induction J generalizing z with
 | nil => rfl
 | cons j J ih => simp only [derive]; rw [ih, ih,show z+step j+u=z+u+step j by abel]
lemma derive_wrap_add {n:Side} (f : Site n → E) (u : Site n) (J : List Axis) (z : Cover) : derive J (fun x=> f (wrap n x+u)) z=derive J f (wrap n z+u):= (derive_period (fun q=> f (q+u)) J z).trans (derive_shift _ _ _ _)
lemma folded (J : List Axis) (x : Site n) : derive J toroid x = ∑ p:Site n,char p x * (topWeight n p * claw J p):=by
 induction J generalizing x with
 | nil => rw [derive,toroid]; apply Finset.sum_congr rfl; intro i _; simp [claw,mul_comm]
 | cons j J ih => simp only [derive]; rw [ih,ih,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p _; rw [char_add]; unfold claw; simp only [List.map_cons, List.prod_cons]; ring
lemma rederive (f : Site n→ℂ) (J : List Axis) (x : Site n) : (derive J f x).re=derive J (fun x=>(f x).re) x:=by
 induction J generalizing x with
 | nil => rfl
 | cons i J ih => rw [derive,derive,Complex.sub_re, ih, ih]
abbrev thread (z : Site n) := (toroid z).re
lemma spin (h : ℝ) (J : List Axis) (x : Site n) : (joint h J x).re = h⁻¹^(J.length+2) * derive J thread x := by
 rw [joint,←folded,← show (↑(h^(-(J.length+2:ℤ))) : ℂ)=(h:ℂ)^(-(J.length+2:ℤ)) from by norm_cast]
 rw [Complex.mul_re, rederive,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
 congr 1
 rw [zpow_neg,← Nat.cast_ofNat (R:=ℤ) (n:=2), ← Nat.cast_add,zpow_natCast,inv_pow]

lemma toll (x : Site n) : (delta (moment x))⁻¹ ≤ (Real.pi^2/4)*(mesh n)⁻¹^2 * (‖incVec 1 (Lattice.lift x)‖^2)⁻¹:=by
 rcases eq_or_ne x 0 with h|h
 · rw [h, show moment (0:Site n)=0 by ext i; simp [moment_apply,Lattice.lift]]; simp [delta]; positivity
 have he:= delta_grade (moment_cube x) (moment_ne h)
 apply he.trans_eq; rw [Real.rpow_neg (norm_nonneg _), ← Nat.cast_ofNat (R:=ℝ) (n:=2), Real.rpow_natCast,moment,norm_span _ mesh_pos,mul_pow]
 simp_rw [inv_pow, mul_inv_rev]; ring
lemma weight_bound (x : Site n) : ‖topWeight n x‖ ≤ ((n.val:ℝ)^4)⁻¹ * ((Real.pi^2/4)*(mesh n)⁻¹^2) * (‖incVec 1 (Lattice.lift x)‖^2)⁻¹ := by
 have hp : 0≤ delta (moment x) := by unfold delta; positivity
 rw [topWeight, ← show (((n.val:ℝ)^(-4:ℤ):ℝ) : ℂ) * (↑((delta (moment x))⁻¹) : ℂ)=(n.val:ℂ)^(-4:ℤ) * (delta (moment x) : ℂ)⁻¹ from by push_cast; rfl, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), zpow_neg]
 erw [zpow_natCast, mul_assoc]; exact mul_le_mul_of_nonneg_left (toll x) (by positivity)
lemma tor_bound (x : Site n) : ‖toroid x‖≤27 := by
 apply (norm_sum_le _ _).trans
 apply (Finset.sum_le_sum (fun (p : Site n) _ => (show ‖topWeight n p * char p x‖ = ‖topWeight n p‖ by rw [norm_mul,norm_char,mul_one]).le.trans (weight_bound p))).trans
 rw [← Finset.mul_sum]
 have h : (∑ p : Site n, (‖incVec 1 (Lattice.lift p)‖^2)⁻¹) = talc n.val n := by rw [talc, inside, Finset.filter_true_of_mem (by intro u hu; exact width u)]
 rw [h]; apply (mul_le_mul_of_nonneg_left (inner_weight n.val) (by positivity)).trans; apply le_of_eq; unfold mesh; field_simp; ring
lemma bounded (D : List Axis) (z : Site n) : |derive D thread z| ≤ 2^D.length*27 := by
 induction D generalizing z with
 | nil => rw [derive,List.length_nil,pow_zero,one_mul]; exact (Complex.abs_re_le_norm _).trans (tor_bound z)
 | cons i d ih => rw [derive, List.length_cons]; apply (abs_sub ..).trans ((add_le_add (ih _) (ih _)).trans (le_of_eq ?_)); ring

lemma far (D : List Axis) : ∃ C>0, ∀ {n:Side},∀ z : Site n, |derive D thread z| * ((pdist z+1:ℝ))^(D.length+2) ≤ C:=by
 obtain ⟨K,hK,H⟩:=upper_tail D (1/2) (by norm_num)
 let s := 4*Real.pi * (D.length+4:ℝ)
 have hs : 0<s := by unfold s; positivity
 let C:= K/s+purse*s^(D.length+2)
 let E:=2^D.length*27*(2*s+1)^(D.length+2)
 refine ⟨max C E,lt_of_lt_of_le (show 0<E by unfold E; positivity) (le_max_right ..),?_⟩
 intro n z
 let a : ℝ:= (pdist z+1:ℝ)
 rcases lt_or_ge a (2*s+1) with hl|hr
 · apply le_trans _ (le_max_right ..); change _ * a ^ _ ≤ E; unfold E; gcongr; apply bounded
 apply le_trans _ (le_max_left ..)
 change _ * a ^ _ ≤ C
 have ha : 0<a:=by unfold a; positivity
 have hh : a⁻¹*s ≤ 1/2 := by rw [inv_mul_eq_div]; apply (div_le_iff₀ ha).2; linarith
 have hnp : (pdist z:ℝ) ≤ (n.val:ℝ) := by exact_mod_cast width z
 have hm : mesh n * ((D.length+4:ℕ):ℝ) ≤ a⁻¹ * s := by
   have hp:= mesh_pos (n:=n)
   have hv : mesh n * a ≤ 4*Real.pi := by
     have h1 : (1:ℝ)≤ n.val:=by exact_mod_cast n.pos
     have h2:= mesh_val (n:=n); apply le_trans (mul_le_mul_of_nonneg_left (show a≤2*n.val by unfold a; linarith) hp.le) (le_of_eq (by linarith only [h2]))
   rw [inv_mul_eq_div, le_div_iff₀ ha,mul_right_comm]; push_cast; unfold s; gcongr
 have hp : 0< pdist z := Nat.pos_of_ne_zero fun h=>by dsimp [a] at hr; rw [h,Nat.cast_zero, zero_add] at hr; linarith only [hr,hs]
 have hv : 1/2 ≤ ‖incVec a⁻¹ (Lattice.lift z)‖ := by
   have hf:= chart_ge (Lattice.lift z); rw [diam_lift] at hf
   rw [norm_span _ (by positivity), inv_mul_eq_div]; apply (le_div_iff₀ ha).mpr; unfold a
   have : (1:ℝ)≤ (pdist z : ℝ) := by exact_mod_cast hp
   linarith
 have hl := lower _ _ hs (show a⁻¹>0 by positivity) (by linarith only [hh]) z D
 have hc : ‖joint a⁻¹ D z‖≤ C := le_trans (by simpa using norm_add_le (joint a⁻¹ D z-piece a⁻¹ s D z) (piece a⁻¹ s D z)) (add_le_add (H (by positivity) hs hh hm z hv) hl)
 have hb := (Complex.abs_re_le_norm _).trans hc
 rw [spin,inv_inv,abs_mul, abs_of_nonneg (pow_nonneg ha.le _),mul_comm] at hb; exact hb
end YM.SchemeRG11.Catch
