import YM.RG11Scheme.Mesh.Clear

/-! Uniform inverse-polynomial decay, including differences of either endpoint (other from translations); required IR bound for one integrated vertex. The GFF here is the *pure gauge-field lattice Laplace* inverse on the period cover. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Mesh
open Lattice Function Filter Set Pert Pert.Full Pert.Band
open scoped Topology BigOperators Classical
variable {n : Side}

variable {E : Type*} [Sub E] {X : Type*} [AddCommGroup X] [One X]
def go (D : List Axis) (f : Four X→E) : Four X→ E := D.rec f (fun i _ u => fun x=> u (x+step i)-u x)
@[simp] lemma starting (f : Four X→E) : go [] f=f := rfl
@[simp] lemma onwards (i D x) (f : Four X→E) : go (i::D) f x= go D f (x+step i)-go D f x := rfl
lemma periodic (D) (f : Site n→ E) (x) : go D (f ∘ wrap n) x=go D f (wrap n x) := by induction D generalizing x with| nil=> rfl| cons i D ih=> simp [ih]
lemma shifted (D) (f : Four X→E) (x p) : go D (fun z=>f (z+x)) p=go D f (p+x) := by induction D generalizing p with| nil=> rfl| cons i D ih=> simp [ih, add_right_comm p]

lemma multiplied (v : Site n) (D) : go D toroid v=∑ p:Site n, char p v * (topWeight n p * claw D p) := by
   induction D generalizing v with
   | nil => simp [toroid,claw,mul_comm]
   | cons i l IH =>
      rw [onwards,IH,IH,←Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun p _=>?_); rw [char_add]; unfold claw; simp only [List.map_cons,List.prod_cons]; ring
lemma torus_joint (v : Site n) (D) (h : ℝ) : (h^(D.length+2))⁻¹ * go D field v = (joint h D v).re := by
   have he (D v) : (go D field v)= (go D toroid (v:Site n)).re := by induction D generalizing v with|nil=>rfl|cons i D ih=> simp only [onwards,ih,Complex.sub_re]
   rw [he,multiplied]; unfold joint
   rw [show (↑h:ℂ)^(-(↑D.length+2:ℤ))=↑((h^(D.length+2))⁻¹) by push_cast; rw [show -(↑D.length+2:ℤ)=-(↑(D.length+2:ℕ):ℤ) by push_cast; rfl,zpow_neg,zpow_natCast]]; rw [Complex.re_ofReal_mul]

lemma settle (D : List Axis) : ∃ C>0,∀ n : Side, Even n.val → ∀ z : Site n, ‖go D field z‖ ≤ C := by
   induction D with
   | nil=> exact upper
   | cons i D ih => obtain ⟨C,hC,H⟩:=ih; exact ⟨C+C,by positivity,fun n e z=> (norm_sub_le (go D field (z+step i)) _).trans (add_le_add (H n e _) (H n e _))⟩

lemma lift_bound (D : List Axis) : ∃ C>0,∀ n : Side,Even n.val → ∀ z:Site n, ‖go D field z‖ ≤ C/wide (lift z)^(D.length+2) := by
    obtain ⟨C,hC,U⟩ := upper_tail D 1 zero_lt_one
    let s:=2*Real.pi*(D.length+4:ℕ)
    obtain ⟨Y,hY,I⟩ := settle D
    have hs : 0<s := by unfold s; positivity
    let d := D.length+2
    have hI : 0<purse := by unfold purse; positivity
    let E := C/s+purse*s^d
    have hp : 0<E := by dsimp only [E]; positivity
    let b:=max (2*s) 1
    refine ⟨E*2^d+Y*(1+b)^d,by unfold b; positivity,?_⟩
    intro n he z
    have hnl:=Full.val_pos n; let L:=‖row (lift z)‖;have hw:=wide_pos (lift z)
    apply (le_div_iff₀ (pow_pos hw _)).2
    by_cases hz : b≤L
    · have hz' : 1 ≤ L := le_trans (le_max_right ..) hz
      have h : 0 < L := by linarith
      let t:=L⁻¹; have ht : 0<t := inv_pos.mpr h
      have hR : 1 ≤ ‖incVec t (lift z)‖ := by rw [inc_row,norm_smul,Real.norm_of_nonneg ht.le,show ‖row (lift z)‖=L from rfl,show t*L=1 from inv_mul_cancel₀ h.ne']
      have hLv : t*s≤1/2 := by unfold t; rw [mul_comm,← div_eq_mul_inv]; apply (div_le_iff₀ h).mpr; linarith only [le_trans (le_max_left .. : 2*s≤max (2*s) 1) hz]
      have hv : mesh n * ((D.length+4:ℕ):ℝ) ≤ t*s := by
        unfold mesh t; rw [div_mul_eq_mul_div,show L⁻¹ * s=s/L by ring]
        exact div_le_div_of_nonneg_left hs.le h (peak_row z)
      let q:=joint t D z
      have hk : ‖q‖ ≤ E := le_trans (by simpa using! norm_add_le (q-piece t s D z) (piece t s D z)) (add_le_add (U ht hs hLv hv z hR) (lower t s hs ht (by linarith) z D))
      have ha : ‖go D field z‖ * L^d ≤ E := by
         have hx : ‖q.re‖ ≤ E := le_trans (Complex.abs_re_le_norm q) hk
         unfold q at hx; rw [← torus_joint, norm_mul, Real.norm_of_nonneg (by positivity)] at hx; simpa only [t,inv_pow,inv_inv,mul_comm] using hx
      have hl : wide (lift z) ≤ 2*L := by unfold wide; linarith only [hz',elev_min (lift z)]
      calc _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw.le hl d) (norm_nonneg _)
           _ = 2^d * (‖go D field z‖ * L^d) := by rw [mul_pow]; ring
           _ ≤ E*2^d := by rw [mul_comm]; gcongr
           _ ≤ _ := le_add_of_nonneg_right (by unfold b; positivity)
    have hh : wide (lift z)≤1+b := by unfold wide; have := lt_of_not_ge hz; linarith only [this,elev_min (lift z)]
    exact (mul_le_mul (I n he z) (pow_le_pow_left₀ hw.le hh _) (by positivity) hY.le).trans (le_add_of_nonneg_left (by positivity))
end YM.RG11Scheme.Mesh
