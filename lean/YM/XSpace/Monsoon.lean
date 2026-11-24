import YM.XSpace.Requite
/-!
# Derivative guard around first chiral point
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function MeasureTheory Filter Set Relief Sail Playpen Trace Litter Octave Lattice Further.FreeCovariance.KP Tide
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v b:E4}{A B C:Toe}{f g h:Breeze}{t:Axis}{k:ℕ}
def waltz (x y:Cover)(v:Toe)(X:Axis):= mov (-step X) v (x-y) -- test tear
lemma eta_chart (c:Shade.Cut)(p:ℝ)(x y z w:Cover)(X:Axis): η X (chart c p x y z B C) w=
  η X (cash c p) (w-x)* (B (w-y)* C (w-z))+waltz w x (cash c p) X*(η X B (w-y)* waltz w z C X+B (w-y)*η X C (w-z)):=by
  have ht (v:Cover): w-step X-v=w-v-step X:= sub_right_comm ..; have hh (v:Toe)(u:Cover): waltz w u v X=v (w-step X-u):= by rw [ht]; change v (-step X+(w-u))=_; rw [sub_eq_add_neg _ (step X),add_comm]; -- ?
  rw [hh,hh]; change cash c p (w-step X-x)*( B (w-step X-y)*C (w-step X-z))-cash c p (w-x)*(B (w-y)*C (w-z))=(cash c p (w-x-step X)-cash c p (w-x))*_+ _*((B (w-y-step X)-B (w-y))* _+ _*(C (w-z-step X)-C (w-z))); simp_rw [ht]; ring
variable (c:Shade.Cut)(s:Stage L a)(X:distance L a x u)(Y:distance L a y v)(Z:distance L a z b) (R:range c u v)(R':range c u b)
lemma broker (c:Shade.Cut)(p:ℝ)(x y z w:Cover)(X:Axis)(h:η X (chart c p x y z B C) w≠0)(hp:0<p)(hP:p≤c.rOut): perch c p (w-x):=by
  by_cases H: chart c p x y z B C w ≠0; exact noncash c _ _ _ _ _ H
  have hh:chart c p x y z B C (w-step X)≠0:= fun H'=> h (by change chart _ _ _ _ _ _ _ _-_=0; change chart c p x y z B C (w-step X)-chart c p x y z B C w=0; rw [H',Classical.not_not.mp H]; simp)
  apply sentinel c _ hp hP X; rw [sub_right_comm]; exact left_ne_zero_of_mul hh
include s X Y Z R R' in
lemma royal (t:Axis)(hy:B∈Terrain 3)(hz:C∈Terrain 3): ∃ D:ℝ,0≤D∧∀ᶠ i in L,∀ w,η t (chart c (a i) (x i) (y i) (z i) B C) w≠0→perch c (a i) (w-x i) ∧ ‖η t (chart c (a i) (x i) (y i) (z i) B C) w‖ ≤ D * a i^7:=by
  obtain ⟨p,hp,P⟩:= make c s t; choose D hD H using fun (k:ℕ) (A:(Terrain k : Set Toe))=> teaches _ A.property _ c.rOut_pos; -- coercion issue
  let E:Breeze:=fun _=> 0; let d:= D 3 ⟨B,hy⟩; let e:= D 3 ⟨C,hz⟩; let o:= D 3 ⟨mov (-step t) C,slide_hill hz _⟩; let f:= D 4 ⟨η t B,down_hill hy _⟩; let g:= D 4 ⟨η t C,down_hill hz _⟩; have hd:0<d:=hD ..; have he:0<e:=hD ..; have ho:0<o:=hD ..; have hf:0<f:=hD ..; have hg:0<g:=hD ..; refine ⟨p*d*e+f*o+d*g,by positivity,?_⟩
  filter_upwards [s.good,s.zero.eventually (ge_mem_nhds c.rOut_pos),P,toll c R X Y,toll c R' X Z] with i hi hh hn ht hr w hw
  let x:= x i; let y:= y i; let z:= z i; let a:= a i; have hh':= broker c a x y z w t hw hi hh; have h1:= resolved c w x y a ht hh'; have h2:= resolved c w x z a hr hh'; have hb:‖B (w-y)‖≤ d*a^3:= H _ ⟨B,hy⟩ a _ hi h1 -- synt
  have hc:‖C (w-z)‖≤ e*a^3:= H _ ⟨C,hz⟩ a _ hi h2; have hb':‖η t B (w-y)‖ ≤ f*a^4:=H (3+1) ⟨_,down_hill hy _⟩ a _ hi h1; have hc': ‖η t C (w-z)‖ ≤ g*a^4:=H (3+1) ⟨_, down_hill hz _⟩ a _ hi h2; have hec: ‖waltz w z C t‖ ≤ o*a^3:= H _ ⟨_,slide_hill hz _⟩ a _ hi h2; have ht:0<a:=hi; refine ⟨hh',?_⟩; rw [eta_chart]; calc
    _ ≤ p*a * (d*a^3*(e*a^3))+(f*a^4*(o*a^3)+(d*a^3)*(g*a^4)):=?_
    _ = _:=by unfold a; ring
  apply (norm_add_le ..).trans (add_le_add ?_ ?_); all_goals rw [norm_mul]
  · rw [norm_mul]; exact mul_le_mul (hn _) (mul_le_mul hb hc (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
  apply (mul_le_of_le_one_left (norm_nonneg _) (by apply cash_fee)).trans; apply (norm_add_le ..).trans (add_le_add ?_ ?_) <;> rw [norm_mul]; exact mul_le_mul hb' hec (norm_nonneg _) (by positivity); exact mul_le_mul hb hc' (norm_nonneg _) (by positivity)
include s in
lemma saw_top {u:E4}(X:distance L a x u)(h:u≠0)(p:Beam k A f)(i:Axis): Tendsto (fun j=> (a j)⁻¹^(k+1) * η i A (x j)) L (𝓝 (-(Maxwell.grad i f u))):=by
  simp_rw [show η i A=-(mov (-step i) (D i A)) from down_phase i,Pi.neg_apply,mul_neg]; exact (shines s X h ((p.step_forth i).moved _)).neg
def source (t:Axis)(u v b:E4)(g h:Breeze)(w:E4):ℝ:= -Maxwell.grad t (fun z=> c z) w * (g (w+u-v)*h (w+u-b))+ c w*((-Maxwell.grad t g (w+u-v))* h (w+u-b)+g (w+u-v)*(-Maxwell.grad t h (w+u-b)))
include s X Y Z R R' in
lemma emergence (hx: Beam 3 A f)(hy: Beam 3 B g)(hz: Beam 3 C h)(t:Axis)[L.IsCountablyGenerated][NeBot L]: Consummate L (fun i=> uses (a i) (x i) A (η t (chart c (a i) (x i) (y i) (z i) B C))) (fun w=> f w * source c t u v b g h w):=by
  refine stormy c s _ _ ?_ hx (royal c s X Y Z R R' t hy.glows hz.glows); filter_upwards [clear_all u v b] with w hw; obtain ⟨_,hc,hC⟩:=hw; let M i:= mark (a i) w; let F i:= M i+x i; have he:distance L a M w:= marks w s.zero s.good; have hy₁:= value (since he X) Y; have hz₁:= value (since he X) Z; have hck(i:ι): -step t + M i=M i-step t:=by abel
  have hu: distance L a (fun i=> M i-step t) w:=by
    unfold distance; simp_rw [Shade.offset_turn]; simpa only [zero_smul,sub_zero] using he.sub (s.zero.smul_const (basis t))
  have hB:= shines s hy₁ hc hy; have hh:= (((muddled c s he t).mul (hB.mul (shines s hz₁ hC hz))).add ((shuffled c hu).mul (((saw_top s hy₁ hc hy t).mul (shines s hz₁ hC (hz.moved (-step t)))).add (hB.mul (saw_top s hz₁ hC hz t)))))
  refine hh.congr fun i=>?_ ; rw [eta_chart]; change _=((a i)⁻¹^7)* (η t (cash _ _) (M i+x i-x i)* (B _ * C _)+ _* _); unfold waltz; simp only [add_sub_cancel_right]; change _=(a i)⁻¹^7* ( _ +cash c (a i) (-step t+(M i))*_) -- check
  rw [hck]; unfold M; ring -- identify
end YM.XSpace.Season
