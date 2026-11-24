import YM.FormalBulk08.Dawn.Parchment

/-! Root preimage pullback in coarse mesh. Does not spend any
volume factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Filter Set Function Laurent Lattice Planned.PrimaryIntegral295
open scoped BigOperators Topology Classical ContDiff
variable {D : ℕ} {L : Side} (x : Site L)

def scale (L : Side) : ℝ := (L.val:ℝ)⁻¹
lemma scale_pos : 0< scale L:= by unfold scale; positivity
lemma scale_melt (h : 2 ≤ L.val) : scale L≤1/2:= by
    unfold scale; rw [←one_div]; gcongr; exact_mod_cast h
lemma scale_small : scale L≤1:= by
    unfold scale; apply inv_le_one_of_one_le₀; exact_mod_cast L.pos
def pith : E4 := scale L • Place.seat (lift x)
lemma pithed : ‖pith x‖≤4 := by
   unfold pith; rw [norm_smul,Real.norm_of_nonneg scale_pos.le]
   have hp : size (lift x) ≤ ∑ _ : Axis,L.val := by
      unfold size; apply Finset.sum_le_sum; intro i _; obtain h:=lift_centers x i; omega
   have h : (size (lift x):ℝ) ≤ 4*L.val := by simpa [Axis] using (show (size (lift x):ℝ)≤(∑ _:Axis,L.val:ℕ) from Nat.cast_le.mpr hp)
   apply (mul_le_mul_of_nonneg_left ((Carrier.shade_seat ..).trans h) scale_pos.le).trans_eq; unfold scale; field_simp

def bay (y : E4) : E4:= pith x+scale L • y
def peninsula (h : 2≤L.val)(y : Pier): Pier:= ⟨bay x y, by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (norm_add_le ..).trans; rw [norm_smul, Real.norm_of_nonneg scale_pos.le]
    have he := still y; have hv := scale_melt h
    nlinarith [pithed x,norm_nonneg y.val,show 0≤scale L from scale_pos.le]⟩

def bowl (f : Garden D): Garden D:= ⟨f.val ∘ bay x,(show ContDiff ℝ D f.val from f.property).comp (show ContDiff ℝ D (bay x) by unfold bay; fun_prop)⟩
lemma ripe (f : E4→ℝ) (d : ℕ) (hf : ContDiff ℝ d f) : iteratedFDeriv ℝ d (f ∘ bay x)=fun y=> scale L^d • iteratedFDeriv ℝ d f (bay x y) := by
   let T:= fun y=> f (pith x + y)
   have he : f ∘ bay x=fun y=>T (scale L • y):=rfl
   rw [he,iteratedFDeriv_comp_const_smul _ (show ContDiff ℝ d T from hf.comp (contDiff_const.add contDiff_id))]
   unfold T; simp_rw [iteratedFDeriv_comp_add_left]; rfl
lemma berry (k : Brush D)(f : Garden D)(z : Pier)(h : 2≤L.val):
    (portrait D (bowl x f)).val k z=(scale L ^ k.1.val)* (portrait D f).val k (peninsula x h z) := by
    change iteratedFDeriv ℝ k.1.val (f.val ∘ bay x) _ _ = _
    rw [ripe x _ _ (tends f k.1)];rfl

/-- Dilation is on the test portrait class, keeps the order D derivative
budget. -/
def tunnel (D : ℕ)(_h :2≤L.val) (p : Studio D) := portrait D (bowl x ((portrayed D p).choose))
lemma tunnel_show (h :2≤L.val) (p : Studio D) (k : Brush D)(z : Pier): (tunnel x D h p).val k z=scale L^k.1.val*(p.val k (peninsula x h z)) := by
    unfold tunnel;rw [berry x k _ z h, (portrayed D p).choose_spec]
lemma tunnel_le (h : 2≤L.val) (p : Studio D): ‖tunnel x D h p‖ ≤ ‖p‖ := by
   refine panel_le _ (norm_nonneg _) fun k z=>?_
   rw [tunnel_show,norm_mul,Real.norm_of_nonneg (pow_nonneg scale_pos.le _)]
   exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ scale_pos.le scale_small)).trans (le_panel ..)

def throughW (D : ℕ)(h : 2≤L.val) : Studio D →L[ℝ]Studio D :=
    LinearMap.mkContinuous (σ:=RingHom.id ℝ) {
       toFun:=tunnel x D h, map_add':=fun p q=> by
          apply Subtype.ext; ext1 i;ext1 z; rw [tunnel_show]; change _*(p.val _ _+q.val _ _) =(tunnel _ _ _ p).val i z+ _
          rw [mul_add,← tunnel_show,← tunnel_show]
       map_smul':=fun a p=> by
          apply Subtype.ext; ext1 i; ext1 z; rw [tunnel_show]
          change _*(a*p.val _ _) = a * (tunnel _ _ _ p).val i z;rw [tunnel_show];ring
    } 1 fun f=> by change ‖tunnel x D h f‖ ≤ 1*_ ; rw [one_mul]; exact tunnel_le x h f
lemma through_show (h : 2≤L.val)(f : Garden D) : throughW x D h (portrait D f)=portrait D (bowl x f) := by
   apply Subtype.ext; ext1 k; ext1 z; change (tunnel x D h _).val _ _ = _; rw [tunnel_show,berry x _ _ z h]
lemma through_le (h:2≤L.val)(p:Studio D): ‖throughW x D h p‖≤‖p‖ := tunnel_le x h p
end YM.FormalBulk08.Dawn
