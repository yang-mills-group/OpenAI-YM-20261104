import YM.SchemeConversionRG11.FirstW.Vane.Face
/-! Integrated cubic density all face rule including inversion price. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {X : Type*} [AddCommGroup X] [One X]
abbrev Sky (G : Gauge) (X : Type*):= Wind G X→ₗ[ℝ] Wind G X →ₗ[ℝ] Wind G X →ₗ[ℝ] ℝ
def spire (G : Gauge) (x : Four X) (a : Walk) := (1/2:ℝ) • (swerve x a (G:=G)+(swerve x a).flip)
def rope (G : Gauge) (x : Four X) (a : Walk) : Sky G X where
 toFun A := (spire G x a).compr₂ ((innerSL ℝ (rail x a A)).toLinearMap)
 map_add' A B := by
   apply LinearMap.ext; intro C; apply LinearMap.ext; intro D; simp
 map_smul' c A:= by
   apply LinearMap.ext; intro C; apply LinearMap.ext; intro D; simp
def wind_dress (L : Sky G X) : Sky G X where
  toFun A := { toFun := fun B=>{ toFun := fun C=> L B C A
                                 map_add' := fun C D=> by simp
                                 map_smul' := fun x B=> by simp }
               map_add' := fun B C=> LinearMap.ext fun D=>by simp
               map_smul' := fun x B=>LinearMap.ext fun C=>by simp }
  map_add' A B:= LinearMap.ext fun C=>LinearMap.ext fun D=>by simp
  map_smul' c A:= LinearMap.ext fun B=>LinearMap.ext fun C=>by simp
def tower (G : Gauge) (x : Four X) (a : Walk) : Sky G X := (-1/48:ℝ) • (rope G x a+wind_dress (rope G x a)+wind_dress (wind_dress (rope G x a)))
lemma tower_eq (A B C : Wind G X) (x) (w) :
 tower G x w A B C=(-1/48)*(inner ℝ (rail x w A) (spire G x w B C) + inner ℝ (rail x w B) (spire G x w C A)+inner ℝ (rail x w C) (spire G x w A B)) := rfl
lemma spire_comm (x : Four X) (w : Walk) (A B : Wind G X) : spire G x w A B=spire G x w B A := by simp only [spire, LinearMap.add_apply,LinearMap.smul_apply,LinearMap.flip_apply]; rw [add_comm]
lemma tower_cycles (A B C : Wind G X) (x) (w) : tower G x w A B C=tower G x w C A B := by rw [tower_eq,tower_eq];ring
lemma tower_sym (A B C : Wind G X) (x) (w) : tower G x w A B C=tower G x w B A C := by rw [tower_eq,tower_eq,spire_comm x w A B,spire_comm x w A C,spire_comm x w C B]; ring
lemma tower_cross (A B C : Wind G X) (x) (w) : tower G x w A B C=tower G x w A C B := by exact (tower_cycles ..).trans (tower_sym ..)
lemma tower_head (A : Wind G X) (x) (w) : tower G x w A A A=(-1/16)*inner ℝ (rail x w A) (swerve x w A A) := by rw [tower_eq]; simp [spire,real_inner_smul_right,inner_add_right];ring
lemma peaks (A : Wind G X) (x) (w) : tower G x w A A A=(-1/48)* iteratedDeriv 3 (fun r=> G.price (travel (pointU A r) x w)) 0 := by
  rw [tower_head]; have he := Pert.First.Tried.square3 (p:=fun r=>travel (pointU A r) x w) (rail_tried A w x) (scan_road w x A); simp only [comp_def] at he; linarith only [he]
lemma steam (A : Orb.Potential G n) :
    wheels (fun x w => tower G x w A.val A.val A.val) = (-1/2:ℝ)*∑ x:Site n,∑ i,∑ j,Pert.First.costVertex x i j A.val := by
  let f (x : Site n) (w : Walk) := tower G x w A.val A.val A.val; change wheels f= _
  rw [wheel_rate]; rotate_left
  · intro x i j; simp only [f,peaks]; simp_rw [swipe_swap _ x i j]
  · intro x i j; simp only [f,peaks]; simp_rw [swipe_flip _ x i j]
  · intro x i; unfold f; rw [tower_head,frontRail]; simp only [lifted_curl,Orb.cur_expand,sub_self,inner_zero_left,mul_zero]
  simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; have he:=Pert.First.mask_third x i j A; unfold Pert.First.price_at at he
  dsimp only [f]; rw [peaks]; split_ifs with h
  · simp only [h,if_true] at he
    simp_rw [Bare.square_links]; change (8:ℝ) * ((-1/48)* iteratedDeriv 3 (fun r:ℝ=> G.price (Orb.plaquette (r • A) x i j)) 0)=_
    rw [he]; ring
  simp only [Pert.First.costVertex,if_neg h,mul_zero]
lemma crown_first (x : Orb.Coords G n) :
    (1/2:ℝ) * wheels (fun o w=> tower G o w (Orb.expand G n x).val (Orb.expand G n x).val (Orb.expand G n x).val) = Pert.First.vertexW x := by rw [steam]; unfold Pert.First.vertexW;ring
lemma direct_free (A : Wind G X) (x) (w) :
  Tendsto (fun r:ℝ=> G.price (travel (pointU A r) x w)/r^2) (𝓝[≠]0) (𝓝 (inner ℝ (rail x w A) (rail x w A)/2)) := by
  rw [real_inner_self_eq_norm_sq]; have H:=rail_tried A w x; obtain ⟨z,e,h,_⟩:=H.slope_eq
  apply Work.F03.price_limit _ (e ▸ h 0); apply G.mat_injective; rw [H.value_eq,G.mat_one] -- arg
lemma flat_spin (A : FullT G n) :
    wheels (fun x w=>inner ℝ (rail x w A) (rail x w A)) = 8* (∑ x,∑ i,∑ j, if i<j then inner ℝ (Orb.cur A x i j) (Orb.cur A x i j) else 0) := by
  rw [wheel_rate]; rotate_left
  · intro x i j; have h:= direct_free A x (icon i j); have he:=direct_free A x (icon j i); simp_rw [swipe_swap _ x i j] at h; exact (div_left_inj' two_ne_zero).mp (tendsto_nhds_unique h he) -- name?
  · intro x i j; have h:=direct_free A x (icon i j); have he:=direct_free A (x+i.vec) (icon i.rev j); simp_rw [swipe_flip _ x i j] at h; linarith only [tendsto_nhds_unique h he]
  · intro x i; simp only [frontRail,lifted_curl,Orb.cur_expand, sub_self,inner_zero_left]
  simp_rw [frontRail,lifted_curl]
lemma flat_cross (A B : FullT G n) : wheels (fun x w=>inner ℝ (rail x w A) (rail x w B)) = 8* (∑ x,∑ i,∑ j, if i<j then inner ℝ (Orb.cur A x i j) (Orb.cur B x i j) else 0) := by
  simp_rw [←lifted_curl,←frontRail]
  have h:= flat_spin (A+B); have ht := flat_spin A; have hw:=flat_spin B
  simp_rw [←lifted_curl,←frontRail] at h ht hw; unfold wheels at h ht hw ⊢
  have hu x (p:Walk) : inner ℝ (rail x p B) (rail x p A)=inner ℝ (rail x p A) (rail x p B) := real_inner_comm ..
  simp only [map_add,inner_add_left,inner_add_right,hu,Finset.sum_add_distrib] at h
  simp_rw [ite_add_zero,Finset.sum_add_distrib] at h -- maybe name
  linarith only [h,ht,hw]
end YM.RG11.FirstW
