import YM.XSpace.Ramble
/-!
# Native angular cost theorem
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Set Filter Lattice Trace Relief Sail Drama
open scoped Topology BigOperators
variable {x y z w u:Cover}{a:Axis}{i:ℕ}{A B C:Toe}
lemma abyss (hx:B∈Terrain 3)(hy:C∈Terrain 3)(h:A∈Terrain i)(he:4<3+i)(x y z:Cover): Summable fun w:Cover=> A (w-z) * pitch B C x y z w := by
  have hp:= form_sum h hx hy (by omega) z x y; exact Summable.of_norm_bounded hp.norm fun w=>by
    unfold pitch Form string; rw [mul_left_comm (A _),norm_mul,Real.norm_of_nonneg (crest ..),mul_assoc]; exact mul_le_of_le_one_left (norm_nonneg _) (dive ..) -- rw mul_assoc ?
lemma seats (hx:B∈Terrain 3)(hy:C∈ Terrain 3)(h:A∈Terrain 3)(a:Axis): ∃ D₀:ℝ,0<D₀∧∀ (x y z:Cover),32* pad (x-y) ≤ pad (x-z) →
   ‖∑' w:Cover,D a A (w-z)*pitch B C x y z w‖≤ D₀ * rate 6 (x-z):=by
  obtain ⟨D,hD,H⟩:=shipping hx hy a; obtain ⟨E,hE,J⟩:=sonar h; refine ⟨128*E*D,by positivity,fun x y z hx' =>?_⟩; let p w:= A (w-z); let q:=pitch B C x y z; set r:=pad (x-z); have hr:0<r:=included _
  rw [show (fun w=> Relief.D a A (w-z)*pitch B C x y z w)=(fun w=> Relief.D a p w*q w) from funext fun w=>by change (A (w-z+_)-_)*_=(A (w+_-z)-_)*_; rw [sub_add_eq_add_sub], duet_dual p q a (by apply (abyss hx hy (slide_hill h (step a)) (by norm_num) x y z).congr; intro w; change A (step a+(w-z))*_ = A (w+step a-z)*_; congr 2; abel) (abyss hx hy h (by norm_num) x y z)]; apply loudest; intro F; rw [← add_zero (_*rate 6 _)]; apply phase (p:=fun w=> η a q w≠0); swap
  · intro W _ he; exact le_of_eq (Finset.sum_eq_zero fun w hw=> by rw [Classical.not_not.mp (he w hw),mul_zero,norm_zero])
  intro W _ h; have he := fun (w:Cover) (hw:w∈W)=> H x y z w hx' (h w hw); calc
   _ ≤ ∑ w∈W, E* rate 3 (w-z)*(D* rate 7 (x-z)):= Finset.sum_le_sum fun w hw=> by rw [norm_mul]; exact mul_le_mul (J _) (he w hw).2 (norm_nonneg _) (mul_nonneg hE.le (sound ..).le)
   _ = E * (∑ w∈W,rate 3 (w-z))*(D*rate 7 (x-z)):=by rw [Finset.mul_sum,Finset.sum_mul]
   _ ≤ (E*(128*r^(4-3:ℕ)))*(D*rate 7 (x-z)):=by
    gcongr; · exact mul_nonneg hD.le (sound ..).le
    exact pc_in (by norm_num) W hr.le fun w hw=>(he w hw).1
   _ = _:=by
     rw [rated,rated]; change _=_*r⁻¹^6; change E*(128*r^1)*(D*r⁻¹^7)=_; field_simp
abbrev haze (A B C: Toe)(x y z:Cover)(w:Cover) := sheer (pad (x-z)) x z A w * string B C x y w
lemma fares_old (hx:B∈Terrain 3)(hy:C∈Terrain 3)(h:A∈Terrain 4)(x y z:Cover): Summable (haze A B C x y z):=by
  apply (((form_sum h hx hy (by norm_num) z x y).sub (abyss hx hy h (by norm_num) x y z)).sub ((easyT hx hy (by norm_num) x y).mul_left (A (x-z)))).congr; intro i; unfold pitch Form haze sheer string; ring
lemma haze_cost (hx:B∈Terrain 3)(hy:C∈ Terrain 3)(h:A∈Terrain 4): ∃ D:ℝ,0<D∧∀ x y z: Cover,
  ‖∑' w:Cover,haze A B C x y z w‖ ≤ D* rate 5 (x-z)*rate 1 (x-y):=by
  obtain ⟨D,hD,H⟩:= shear h; obtain ⟨E,hE,K⟩:= sonar hx; obtain ⟨G,hG,J⟩:=sonar hy; refine ⟨D*E*G*16384,by positivity, fun x y z=> ?_⟩; let F := haze A B C x y z; apply loudest; intro Q; let P:=D* rate 5 (x-z); have hp : 0 < P:=mul_pos hD (sound ..); let R:= P*E*G; have hr:0<R:=by unfold R; positivity
  have ht (w:Cover): ‖F w‖≤ R*(rate 2 (w-x)*rate 3 (w-y)):=by
    unfold F haze string; simp_rw [norm_mul]; refine (mul_le_mul (H x z w) (mul_le_mul (K _) (J _) (norm_nonneg _) (mul_nonneg hE.le (sound ..).le)) (by positivity) (mul_nonneg hp.le (included _).le)).trans_eq ?_ ; unfold R P; rw [← moon_paid 2 (w-x)]; ring
  exact (Finset.sum_le_sum fun i (_:i∈Q)=> ht i).trans (by rw [← Finset.mul_sum]; refine (mul_le_mul_of_nonneg_left (pay_duet (by norm_num) (by norm_num) (by norm_num) Q x y) hr.le).trans_eq ?_; unfold R P; norm_num; ring)
lemma beyond (hx:B∈Terrain 3)(hy:C∈Terrain 3)(h:A∈Terrain 4)(x y z:Cover):
     Trail z x y A B C-A (x-z)*res B C x y=(∑' w:Cover, A (w-z)*pitch B C x y z w)+ ∑' w:Cover,haze A B C x y z w :=by
  unfold Trail res; rw [← tsum_mul_left,← (abyss hx hy h (by norm_num) x y z).tsum_add (fares_old hx hy h x y z),← (form_sum h hx hy (by norm_num) z x y).tsum_sub (show Summable _ from (easyT hx hy (by norm_num) x y).mul_left (A (x-z)))]; apply tsum_congr; intro i; unfold Form pitch string haze sheer string; ring -- unfold dup?
abbrev Timed (A B C:Toe):=∃ D:ℝ,0≤D∧∀ x y z:Cover,32*pad (x-y)≤pad (x-z)→ ‖Trail z x y A B C-A (x-z)*res B C x y‖ ≤ D*rate 5 (x-z)*rate 1 (x-y)
lemma balanced (hx:B∈Terrain 3)(hy:C∈Terrain 3)(h:A∈Terrain 3)(a:Axis): Timed (D a A) B C:=by
  obtain ⟨D,hD,H⟩:= seats hx hy h a; obtain ⟨E,hE,K⟩:= haze_cost hx hy (steps_hill h a); refine ⟨D+E,(add_pos hD hE).le,fun x y z ht=>?_⟩; rw [beyond hx hy (steps_hill h a),add_mul,add_mul]; apply (norm_add_le ..).trans (add_le_add ((H x y z ht).trans ?_) (K x y z)); have hp:= included (x-y); rw [← moon_mul 5 1, mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (moon_mono 1 (by linarith)) (sound ..).le) hD.le
private def finale (hx:B∈Terrain 3)(hy:C∈ Terrain 3): Submodule ℝ Toe where
 carrier:={A| A∈Terrain 4∧ Timed A B C}
 zero_mem':=⟨Submodule.zero_mem _,⟨0,le_rfl,fun i h w _ =>by simp [Trail,Form]⟩⟩
 add_mem' :=by
  rintro A H ⟨h,C,hC,X⟩ ⟨h',D,hD,Y⟩; refine ⟨Submodule.add_mem _ h h', ⟨C+D, add_nonneg hC hD, fun x y z he=>?_⟩⟩; rw [trail_add h h' hx hy (by norm_num), Pi.add_apply,add_mul,add_mul,add_mul,add_sub_add_comm]; exact (norm_add_le ..).trans (add_le_add (X _ _ _ he) (Y _ _ _ he))
 smul_mem' :=by
   rintro r A ⟨h,C,hC,X⟩; refine ⟨Submodule.smul_mem _ _ h,⟨‖r‖ *C,by positivity,fun x y z he=>?_⟩⟩; rw [trail_smul,Pi.smul_apply,smul_eq_mul,mul_assoc r,← mul_sub,norm_mul]; exact (mul_le_mul_of_nonneg_left (X _ _ _ he) (norm_nonneg _)).trans_eq (by ring)
theorem of_probe (hx:B∈ Terrain 3)(hy:C∈ Terrain 3)(he:A∈Surface 3) : Timed A B C:= (surfaces_p (finale hx hy) (fun f h i=>⟨steps_hill h i,balanced hx hy h i⟩) he).2
end YM.XSpace.Octave
