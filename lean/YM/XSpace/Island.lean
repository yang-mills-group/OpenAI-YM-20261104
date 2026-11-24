import YM.XSpace.Monsoon
/-!
# Infinite-age exterior convergence
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function MeasureTheory Filter Set Relief Sail Playpen Trace Litter Octave Lattice Further.FreeCovariance.KP Tide
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v b:E4} {A B C: Toe} {f g h: Breeze}{k:ℕ}
variable (c:Shade.Cut)
abbrev strip (a:ℝ)(x:Cover):=1-cash c a x
def later (a:ℝ)(x:Cover)(A:Toe)(w:Cover):ℝ:=strip c a (w-x)*A (w-x)
lemma strip_norm (p:ℝ)(x:Cover): ‖strip c p x‖ ≤1:=by rw [Real.norm_of_nonneg (sub_nonneg.mpr (higher c p x))]; linarith [lower c p x]
variable (s: Stage L a)(X:distance L a x u)
include s X in
lemma pays (hx: A∈Terrain k)(hh:2≤k): ∃ C:ℝ, 0<C∧∀ᶠ i in L,∀ t:E4, ‖(a i)⁻¹^k*later c (a i) (x i) A (mark (a i) t)‖ ≤ C*(1+‖t‖)⁻¹^2:=by
  obtain ⟨C,hC,H⟩:= sonar hx; let D:=‖u‖+1; let b:=c.rIn; have hb:0<b:=c.rIn_pos; set Q:=2*((3+D)/b+1); have hd:0<D:=by unfold D; positivity
  have hp:0<Q:=by unfold Q; positivity
  refine ⟨C*Q^k,by positivity,?_⟩; filter_upwards [X.norm.eventually (ge_mem_nhds (lt_add_one ..)), s.good,s.zero.eventually (ge_mem_nhds zero_lt_one)] with i hi ht hi' t; let p:=a i; let X:=x i; let w:=mark p t; unfold later; rw [norm_mul,norm_mul]; by_cases he:strip c p (w-X)=0; · rw [he,norm_zero,zero_mul,mul_zero]; positivity
  have h := exc c p (w-X) (fun e=> he (by unfold strip; rw [e,sub_self])); let y:=actual p X; let L:=pad (w-X); let E:=actual p (w-X); have hl:0<L:=Drama.included _; let z:=actual p w; have he': E+y=z:=by unfold E; rw [ar_sub,sub_add_cancel]
  have hE : ‖E‖ ≤ 2*p *L := by apply (Shade.size_actual ht (w-X)).2.trans; gcongr; change _≤1+_; simp
  have he₂:b≤‖E‖:=h; have he₃:‖y‖≤D:=hi; have ht' : 0<p:=ht; have hz:1+‖t‖ ≤ Q * (p * L):=calc
    _ ≤ 1+ (‖E‖+D+2*p):=by
      apply add_le_add le_rfl; have h:=norm_sub_norm_le t z; rw [norm_sub_rev] at h; have h':‖z-t‖≤2*p:= current p ht t; linarith [show ‖z‖≤‖E‖+‖y‖ from he' ▸ norm_add_le E y]
    _ ≤ _:=by unfold Q; calc
       _ ≤ 3+D+ (2*p*L):=by change p≤1 at hi'; linarith
       _ ≤ ((3+D)/b+1)*(2*p*L):=by rw [add_mul,one_mul]; gcongr; field_simp; nlinarith [show b≤2*p*L from he₂.trans hE]
       _ = _:=by ring
  change ‖p⁻¹^k‖* _ ≤ _; rw [Real.norm_of_nonneg (by positivity : 0≤ p⁻¹^k)]; refine (mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (norm_nonneg _) (strip_norm ..)).trans (H (w-X))) (by positivity : 0≤ p⁻¹^k)).trans ?_; calc
    _ = C*(p*L)⁻¹^k:=by rw [rated]; change _ * (C*L⁻¹^k)=_; field_simp; ring
    _ ≤ C* (Q*(1+‖t‖)⁻¹)^k := by gcongr; field_simp; nlinarith
    _ ≤ _:=by rw [mul_pow, ← mul_assoc]; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by simp)) hh) (by positivity)

def older (u:E4)(f:Breeze)(t:E4):=(1-c (t-u))*f (t-u)
include c s X in
lemma late (t:E4)(h:t≠u)(f: Breeze)(hx:Beam k A f): Tendsto (fun i=> (a i)⁻¹^k*later c (a i) (x i) A (mark (a i) t)) L (𝓝 (older c u f t)):=by
  have he:= value (marks t s.zero s.good) X; exact ((tendsto_const_nhds (x:=(1:ℝ))).sub (shuffled c he) |>.mul (shines s he (sub_ne_zero.mpr h) hx)).congr fun _=> mul_left_comm ..
def drape (a:ℝ)(x y z:Cover)(A B C:Toe): Toe:= fun w=> a⁻¹^6*(later c a x A w * later c a y B w *later c a z C w)
def suburb (u v b:E4)(f g h:Breeze): Breeze:= fun t=> older c u f t * older c v g t * older c b h t
include c in
lemma sums_ext (x y z:Cover)(a:ℝ)(Hx:A∈Terrain 4)(Hy:B∈Terrain 3)(Hz:C∈Terrain 3): Summable (drape c a x y z A B C):=by
  apply Summable.mul_left; refine Summable.of_norm_bounded (form_sum Hx Hy Hz (by norm_num) x y z).norm fun w=>?_ ; unfold later Form; simp only [norm_mul]; gcongr <;> exact mul_le_of_le_one_left (norm_nonneg _) (strip_norm ..)
include c s X in
lemma suburb_cost (Y:distance L a y v)(Z:distance L a z b)(hx:Beam 4 A f)(hy:Beam 3 B g)(hz:Beam 3 C h)[L.IsCountablyGenerated][NeBot L]: Consummate L (fun i=> drape c (a i) (x i) (y i) (z i) A B C) (suburb c u v b f g h):= by
  have he(i:ι)(t:E4): down (drape c (a i) (x i) (y i) (z i) A B C) (a i) t=((a i)⁻¹^4 * later c (a i) (x i) A (mark (a i) t))*((a i)⁻¹^3 * later c (a i) (y i) B (mark (a i) t))*((a i)⁻¹^3 * later c (a i) (z i) C (mark (a i) t)):=by unfold down drape; ring
  obtain ⟨D,hD,H⟩:= pays c s X (show A∈Terrain 4 from hx.glows) (by norm_num); obtain ⟨E,hE,J⟩:= pays c s Y (show B∈Terrain 3 from hy.glows) (by norm_num); obtain ⟨F,hF,K⟩:=pays c s Z (show C∈Terrain 3 from hz.glows) (by norm_num); apply prince s (Stall.paid.const_mul (D*E*F)) ?_ ?_
  · filter_upwards [H,J,K] with i hi hh hv; refine Eventually.of_forall fun x=>?_ ; rw [he,norm_mul,norm_mul ((a i)⁻¹^4*_)]; exact (mul_le_mul (mul_le_mul (hi x) (hh x) (norm_nonneg _) (by positivity)) (hv x) (norm_nonneg _) (by positivity)).trans_eq (by unfold Stall.tax; ring)
  filter_upwards [remaining u,remaining v,remaining b] with t hu hv hb; exact (((late c s X _ hu _ hx).mul (late c s Y _ hv _ hy)).mul (late c s Z _ hb _ hz)).congr fun i=>(he i t).symm
end YM.XSpace.Season
