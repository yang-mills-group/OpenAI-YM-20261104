import YM.UVExt.AlphaSeparation

/-! Intertwining replicated fields on two exact periods. Here the quotient reduces a torus modulo n (NOT blocking with some new averaging); equality of the periodized slots uses wrap on the whole path assignment. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths.Covering
open Filter Lattice RG Wilson Laurent Matrix Set Function Exterior Precision Bid
open scoped ContDiff Topology BigOperators Classical
variable {n m : Side} {G : Gauge}
structure Tiles (n m : Side) where
   paid : n.val ∣ m.val
variable (h : Tiles n m)
def Tiles.quot (h : Tiles n m) : Site m →+ Site n where
  toFun u := (ZMod.castHom h.paid (Per n)) ∘ u
  map_zero' := funext fun i=> (ZMod.castHom h.paid _).map_zero
  map_add' a b := funext fun i=> map_add (ZMod.castHom h.paid _) (a i) (b i)
lemma fold_wrap (v : Cover) : h.quot (wrap m v)=wrap n v := funext fun i=> map_intCast (ZMod.castHom h.paid (Per n)) _
lemma fold_onto : Function.Surjective h.quot := fun i => ⟨wrap m (lift i),by rw [fold_wrap,wrap_lift]⟩
def quota (_ : Tiles n m) : ℝ := ((m.val:ℝ)/(n.val:ℝ))^4
def weightCut (h : Tiles n m) (f : Site n→ℝ) := ∑ i:Site m, f (h.quot i)
protected lemma Tiles.alloc (g : Site n→ℝ) : weightCut h g=quota h * ∑ i:Site n,g i := by
   classical
   let S := { x : Site m // h.quot x = (0 : Site n) }
   have same (x : Site n) : Fintype.card {y : Site m // h.quot y=x}=Fintype.card S := by
       obtain ⟨y,hy⟩ := fold_onto h x
       apply Fintype.card_congr {
          toFun u := (⟨u.val-y,by simp only [map_sub,hy,u.2,sub_self]⟩ : S)
          invFun p := ⟨p.val+y, by simp only [map_add,p.property,hy,zero_add]⟩
          left_inv x := Subtype.ext (sub_add_cancel ..)
          right_inv x := Subtype.ext (add_sub_cancel_right ..)
       }
   let Z := Equiv.sigmaFiberEquiv h.quot
   have total (g : Site n→ℝ) : weightCut h g = (∑ x:Site n, (Fintype.card S : ℝ)*g x) := by
      unfold weightCut; refine Eq.trans (Z.sum_comp _).symm ((Fintype.sum_sigma _).trans (Finset.sum_congr rfl fun i _=> ?_))
      rw [show (∑ e:{e₀:Site m // h.quot e₀=i}, (g (h.quot (Z ⟨i,e⟩))))=∑ e:{e₀: Site m//h.quot e₀=i},g i from Finset.sum_congr rfl fun e _=>congr_arg g e.2]; simp [same]
   suffices (Fintype.card S:ℝ)=quota h by rw [total,←Finset.mul_sum,this]
   have he := total (fun _ : Site n=>1)
   simp only [weightCut, site_card,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_pow,mul_one] at he
   unfold quota; rw [div_pow]; exact (eq_div_iff (pow_ne_zero _ (by exact_mod_cast n.property.ne'))).mpr ((mul_comm ..).trans he.symm)

def Tiles.copies {α} (U : Links (Per n) α) := fun t : Edge (Site m) => U (h.quot t.1,t.2)
def Tiles.clone (u : Dir G n) : Dir G m := fun t=>u (h.quot t.1,t.2)
lemma affine_cut (s : Signed) (b x : Site m) : h.quot (affine s b x)=affine s (h.quot b) (h.quot x) := by
 unfold affine
 rw [map_add,←wrap_lift x,wrap_signed,fold_wrap,fold_wrap,wrap_signed]
 -- done
lemma vec_cut (a : Step) : h.quot a.vec=a.vec := by rw [← wrap_vec m a,fold_wrap,wrap_vec]
lemma step_cut (i : Axis) : h.quot (step i)=step i := by rw [← wrap_step m i,fold_wrap,wrap_step]
lemma pull_copied (U : Config G n) (s : Signed) (b : Site m) : pull s b (h.copies U) = h.copies (pull s (h.quot b) U) := by
    funext e
    simp only [pull,Tiles.copies,Step.read,Step.used]
    split_ifs <;> simp only [map_sub,affine_cut,step_cut]
lemma area_copy (U : Config G n) (x : Site m) : expandAt x (h.copies U)=expandAt (h.quot x) U := by funext e; simp only [expandAt,Tiles.copies,map_add,fold_wrap]
lemma copy_motion (x:ℝ) (u : Dir G n) : represent (x • h.clone u)=h.copies (represent (x • u)) := by unfold represent; rfl
lemma copy_slot {j : ℕ} (a : RG.Atom G j) (b : Site m) (U : Config G n) : a.unmasked (h.copies U) b=a.unmasked U (h.quot b) := by unfold RG.Atom.unmasked Slot.atSite; simp only [area_copy]

lemma loop_per (R : PathData G) (U : Config G n) : Precision.loop R (h.copies U)=quota h * Precision.loop R U := by
    unfold Precision.loop Patch.average
    change (Fintype.card Signed:ℝ)⁻¹ * (∑ i:Signed,_) = (quota h) * ((Fintype.card Signed:ℝ)⁻¹ * (∑ i:Signed,_))
    rw [mul_left_comm (quota h)]
    apply congr_arg ((Fintype.card Signed:ℝ)⁻¹ * ·)
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl fun q hq=> ?_
    try dsimp only [] -- try
    rw [pull_copied,map_zero]
    unfold uncut; refine Eq.trans ?_ (h.alloc _)
    exact Finset.sum_congr rfl fun i _=>tsum_congr fun j=> copy_slot ..

lemma loop_per_shadow {K : Shadow G} {M : ℕ→PathData G} {τ C σ p} (e : Passing M K σ C τ p) (v : Dir G n) (j) : tag j (spiral K (h.clone v))=quota h*tag j (spiral K v) := by
    apply tendsto_nhds_unique (e.flow_loop (h.clone v)) ((show Tendsto (fun i=> quota h * _) _ (𝓝 _) from (e.flow_loop (q:=j) v).const_mul (quota h)).congr' _)
    filter_upwards [e.mask] with i hi
    have he : spiral (wick (M i)) (h.clone v)=(quota h) • spiral (wick (M i)) v := by rw [spiral_loop _ _ hi,spiral_loop _ _ hi]; simp_rw [copy_motion,loop_per]; rfl
    rw [he]; exact (iteratedDeriv_const_smul ((spiral_smooth _ (shadow_pay _ hi) e.width v).contDiffAt.of_le (finite_cap _)) (quota h) : tag _ _=_).symm
end YM.UVExt.Paths.Covering
