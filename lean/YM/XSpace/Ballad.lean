import YM.XSpace.Dolphin
/-!
# Leg operator estimate & its gradient transfer (all scales)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Asymptotics Set Filter Lattice Trace Relief Sail Tide Scale
open scoped Topology BigOperators
variable {i j k:ℕ}{A B C D₀:Toe}
lemma sonar (h:A∈Terrain i):∃ C:ℝ,0<C∧∀ w, ‖A w‖≤ C*rate i w:= virgin h
lemma easyT (hx:A∈Terrain i)(hy:B∈Terrain j)(he:4< i+j)(x y:Cover) : Summable fun w:Cover=> A (w-x)* B (w-y):=by
  obtain ⟨C,hC,H⟩:= sonar hx; obtain ⟨D,hD,K⟩:=sonar hy; refine Summable.of_norm_bounded ((duet_free (x:=x) (y:=y) he).mul_left (C*D)) (fun v=>?_); rw [norm_mul]; exact (mul_le_mul (H _) (K _) (norm_nonneg _) (mul_nonneg hC.le (sound ..).le)).trans_eq (mul_mul_mul_comm ..)
abbrev Form (x y z:Cover)(A B C:Toe):= fun w:Cover=> A (w-x)* B (w-y) * C (w-z)
abbrev Trail (x y z: Cover)(A B C:Toe):= ∑' w:Cover,Form x y z A B C w
lemma sonar3 (hx:A∈ Terrain i)(hy:B∈Terrain j)(hz:C∈ Terrain k) : ∃ D:ℝ,0≤D ∧ ∀ x y z w, ‖Form x y z A B C w‖ ≤ D*‖Form x y z (rate i) (rate j) (rate k) w‖:=by
  obtain ⟨p,hp,P⟩:=sonar hx; obtain ⟨q,hq,Q⟩:=sonar hy; obtain ⟨r,hr,R⟩:=sonar hz; refine ⟨p*q*r,by positivity,fun x y z w=>?_⟩; unfold Form; rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sound ..).le (sound ..).le) (sound ..).le),norm_mul,norm_mul]; exact (mul_le_mul (mul_le_mul (P _) (Q _) (norm_nonneg _) (mul_nonneg hp.le (sound ..).le)) (R _) (norm_nonneg _) (mul_nonneg (mul_nonneg hp.le (sound ..).le) (mul_nonneg hq.le (sound ..).le))).trans_eq (by ring)
lemma form_sum (hx:A∈ Terrain i)(hy:B∈Terrain j)(hz:C∈ Terrain k)(he:4< i+j)(x y z:Cover):Summable (Form x y z A B C):= by
  obtain ⟨D,hD,H⟩:=sonar3 hx hy hz; exact Summable.of_norm_bounded ((chord_free he k).norm.mul_left D) (H x y z)
lemma trail_add (hx:A∈Terrain i)(hz:D₀∈Terrain i)(hy:B∈ Terrain j)(h:C∈ Terrain k)(he:4< i+j)(x y z:Cover) : Trail x y z (A+D₀) B C=Trail x y z A B C+ Trail x y z D₀ B C:=by
  unfold Trail; rw [← Summable.tsum_add (form_sum hx hy h he x y z) (form_sum hz hy h he x y z)]; exact tsum_congr fun w=> by unfold Form; rw [Pi.add_apply,add_mul,add_mul]
lemma trail_smul (x y z:Cover)(n:ℝ)(a b c:Toe) : Trail x y z (n • a) b c=n*Trail x y z a b c:=by unfold Trail; rw [← tsum_mul_left]; exact tsum_congr fun w=> by unfold Form; rw [Pi.smul_apply,smul_eq_mul]; ring
lemma form_flip (A B C:Toe)(x y z:Cover): Form y x z B A C=Form x y z A B C:=by ext1 i; unfold Form; ring
lemma form_turn (A B C:Toe)(x y z:Cover): Form y z x B C A=Form x y z A B C:=by ext1 i; unfold Form; ring
-- adjoint. either support method or power Method
lemma duet_dual (p q:Toe)(a:Axis)(hp:Summable (fun w:Cover=>p (w+step a)*q w))(h:Summable (fun w:Cover=> p w*q w)) :
   ∑' w: Cover, D a p w * q w = ∑' w:Cover, p w * η a q w :=by
  let V:=Equiv.subRight (step a : Cover) -- test
  have he(w:Cover):p (V w+step a)*q (V w)=p w*q (w-step a):=by change p (w-step a+step a)*_= _; rw [sub_add_cancel]; rfl
  have hq:Summable (fun w:Cover=>p w*q (w-step a)):= ((Equiv.summable_iff V).mpr hp).congr he
  rw [show (fun w=>D a p w * q w)=(fun w:Cover=>p (w+step a)*q w-p w*q w) from funext fun w=> sub_mul .., hp.tsum_sub h,show (fun w=> p w * η a q w)=(fun w=> p w*q (w-step a)-p w*q w) from funext fun w=> mul_sub .., hq.tsum_sub h, ← Equiv.tsum_eq V (fun w=>p (w+step a)*q w)]; simp_rw [he]
lemma tune_dual (hx:A∈Terrain i)(hy:B∈ Terrain j)(hz:C∈Terrain k)(he:4< i+j)(x y z:Cover)(a:Axis): Trail x y z (D a A) B C=
    Trail x y z A (η a B) (mov (-step a) C)+Trail x y z A B (η a C):=by
  let p := mov (-x) A; let b:=mov (-y) B; let c:=mov (-z) C; have he' (w v:Cover): -w+v=v-w:=(by abel); have h (w:Cover): p (w+step a)=mov (step a) A (w-x):=by change A (-x+_)=A (_+_); congr 1; abel
  have hV:= duet_dual p (b*c) a ?_ ?_
  · unfold Trail; rw [← (form_sum hx (down_hill hy a) (slide_hill hz _) (by omega) x y z).tsum_add (form_sum hx hy (down_hill hz a) he x y z)]; trans ∑' w:Cover,D a p w * (b*c) w; apply tsum_congr; intro w; change (A (w-x+step a)-_)*_*_=(p (w+_) -p w)*(b w*c w); change _=(A (-x+(w+_))-A (-x+w))*(B (-y+w)*C (-z+w)); simp only [he', sub_add_eq_add_sub]; ring
    rw [hV]; apply tsum_congr; intro w; change A (-x+w)*( (B (-y+(w-step a))*C (-z+(w-step a)))- B (-y+w)* C (-z+w))= A (w-x)*(B (w-y-step a)-B (w-y))*C (-step a+(w-z))+ A (w-x)* B (w-y)*(C (w-z-step a)-C (w-z)); simp only [he']; rw [sub_right_comm w (step a) y,sub_right_comm w (step a) z]; ring
  · exact (form_sum (slide_hill hx (step a)) hy hz he x y z).congr fun w=>by rw [h]; unfold Form; change _= _ *(B (-y+w)*C (-z+w)); simp only [he']; rw [mul_assoc]
  exact (form_sum hx hy hz he x y z).congr fun w=>by unfold Form; change _= A (-x+w)*(B (-y+w)*C (-z+w)); simp only [he']; rw [mul_assoc]

variable {ι:Type}{a:ι→ℝ}{L:Filter ι}{x y z:ι→Cover}(s:Relief.Stage L a)(H:Ensemble L a x y z) (hx:A∈Terrain i)(hy:B∈Terrain j)(hz:C∈Terrain k)
include s H in
lemma toll3 (hx:A∈ Terrain i)(hy:B∈Terrain j)(hz:C∈ Terrain k)(hxy:4< i+j)(hxz:4< i+k)(hi:i≤4)(hj:j≤4)(hk:k≤4): Priced L a (i+j+k-4) (fun t=>Form (x t) (y t) (z t) A B C):=by
  obtain ⟨C,hC,h⟩:= sonar3 hx hy hz; exact tango (jamb s H hi hj hk hxy hxz) hC (Eventually.of_forall fun i w _=> h (x i) (y i) (z i) w)
-- Surface gets SIGNED only.
def gift (x y z:ι→Cover)(B C:Toe)(A:Toe):Prop:= Little L a 6 (fun i=> Trail (x i) (y i) (z i) A B C) -- free L a missing
include B C in -- edit
private def green (L:Filter ι)(a:ι→ℝ)(x y z:ι→Cover)(hy:B∈Terrain 3)(hz:C∈ Terrain 3): Submodule ℝ Toe where
  carrier:= {A| A∈Terrain 5 ∧ gift (L:=L) (a:=a) x y z B C A}
  zero_mem':= ⟨Submodule.zero_mem _,show Little L a 6 _ from (isLittleO_zero _ L).congr (fun i=> by simp [Trail,Form]) (fun _=>rfl)⟩
  add_mem' := fun A B'=> by -- type?
    exact ⟨Submodule.add_mem _ A.1 B'.1, (IsLittleO.add A.2 B'.2).congr (fun i=> (trail_add A.1 B'.1 hy hz (by norm_num) (x i) (y i) (z i)).symm) (fun _=>rfl)⟩
  smul_mem' := by intro c p hp; exact ⟨Submodule.smul_mem _ _ hp.1, (IsLittleO.const_mul_left hp.2 c).congr (fun i=> (trail_smul ..).symm) (fun _=>rfl)⟩
include s H in
lemma surf (hy:B∈Terrain 3)(hz:C∈ Terrain 3)(V:A∈Surface 4): gift (L:=L) (a:=a) x y z B C A:= by
  suffices Surface 4≤green L a x y z hy hz from (this V).2; refine surfaces_p _ (fun f h a=>⟨steps_hill h a,?_⟩); unfold gift; simp_rw [tune_dual h hy hz (by norm_num)]; exact (pull s (toll3 s H h (down_hill hy a) (slide_hill hz _) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))).add (pull s (toll3 s H h hy (down_hill hz a) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
end YM.XSpace.Octave
