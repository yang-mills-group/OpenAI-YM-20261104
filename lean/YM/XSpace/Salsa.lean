import YM.XSpace.Verse
import YM.XSpace.Liken
/-!
# Corridors of three-line contact budgets (half-exponent currency)

 The price on the absolute sum is needed even for using the full score (Gram & positions) before extracting the triangle. Some sites get limits of the signed sum instead for borderline powers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Asymptotics Filter Set Lattice Trace Relief Sail
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{V:Type*} [Norm V] {S:ι→Cover→Prop}
-- keep integrable signatures. eventually only; many terms no need sum before.
abbrev swing (a:ℝ):= Real.sqrt a⁻¹ -- parse sqrt of inverse OR (sqrt a)^-1? test
abbrev tariff (k:ℕ)(a:ℝ):=a^k *swing a
def Dance (S:ι→ Cover→Prop)(L:Filter ι)(a:ι→ℝ)(k:ℕ)(F:ι→Cover→V): Prop:= ∃ C:ℝ,0≤C∧∀ᶠ i in L,∀ s:Finset Cover,(∀ w∈s,S i w) →∑ w∈s, ‖F i w‖ ≤ C * tariff k (a i)
variable {F:ι→Cover→V}{x y z:ι→Cover}{i j k:ℕ}
lemma salsa {T:ι→Cover→Prop}(h:Dance S L a k F)(he:∀ᶠ i in L,∀ x,T i x→ S i x): Dance T L a k F:=by obtain ⟨C,hC,H⟩:= h; exact ⟨C,hC,(H.and he).mono fun i hi B h=> hi.1 B fun x hx=> hi.2 x (h x hx)⟩
abbrev Priced (L:Filter ι)(a:ι→ℝ)(k:ℕ)(F:ι→Cover→V): Prop:= Dance (fun _ _=>True) L a k F
lemma tango {T:Type*}[Norm T]{G:ι→Cover→T}{B:ℝ}(h:Dance S L a k F)(hb:0≤B)(H:∀ᶠ i in L,∀ x,S i x→ ‖G i x‖≤ B*‖F i x‖): Dance S L a k G:= by
  obtain ⟨C,hC,K⟩:= h; refine ⟨B*C,mul_nonneg hb hC,?_⟩; filter_upwards [K,H] with i hi ht W hW; exact (Finset.sum_le_sum (fun j hj=> ht j (hW j hj))).trans (by rw [← Finset.mul_sum,mul_assoc B C]; exact mul_le_mul_of_nonneg_left (hi W hW) hb)
-- ∀ poses packing sequential
structure Ensemble (L:Filter ι)(a:ι→ℝ)(x y z:ι→Cover): Prop where
 xy:distFee L a (fun i=>x i-y i)
 xz:distFee L a (fun i=>x i-z i)
 yz:distFee L a (fun i=>y i-z i)
lemma distSym (h:distFee L a (fun i=>x i-y i)):distFee L a (fun i=>y i-x i):= by obtain ⟨C,hC,H⟩:=h; exact ⟨C,hC,H.mono fun i hi=> by change C≤a i*pad (y i-x i); rw [sym]; exact hi⟩
lemma band (h:Ensemble L a x y z): Ensemble L a z x y:= ⟨distSym h.xz,distSym h.yz,h.xy⟩
lemma rhythm (h:Ensemble L a x y z): Ensemble L a y x z:=⟨distSym h.xy,h.yz,h.xz⟩
def Beats (S:ι→Cover→Prop)(L:Filter ι)(a:ι→ℝ)(x:ι→Cover): Prop:=∃ C:ℝ,0<C∧∀ᶠ i in L,∀ w,S i w→ C≤ a i * pad (w-x i)
variable (s:Relief.Stage L a)
include s in
lemma jitter {P:ι→ℝ→Prop} {C:ℝ}(hC:0<C)(H:∀ᶠ i in L,P i (C/a i))(h:∀ᶠ i in L,∀ D:ℝ,1≤D→P i D→∀ B:Finset Cover,(∀ w∈B,S i w) → ∑ w∈B, ‖F i w‖ ≤524288* D⁻¹^k*Real.sqrt D): Dance S L a k F:=by
  refine ⟨524288*C⁻¹^k*Real.sqrt C,by positivity,?_⟩; filter_upwards [s.zero.eventually (ge_mem_nhds hC), s.good,H,h] with i hi ht hh hv B hB; exact (hv _ ((le_div_iff₀ ht).2 (by linarith)) hh B hB).trans_eq (by unfold tariff swing; rw [Real.sqrt_div hC.le, inv_div, Real.sqrt_inv, div_eq_mul_inv (a i),mul_pow,div_eq_mul_inv]; ring)
include s in
lemma jamb (e:Ensemble L a x y z)(hi:i≤4)(hj:j≤4)(hk:k≤4)(he:4< i+j)(hv:4< i+k) :
  Priced L a (i+j+k-4) (fun t w=>rate i (w-x t)*rate j (w-y t)*rate k (w-z t)):=by
  obtain ⟨Cx,hx,Hx⟩:=e.xy; obtain ⟨Cy,hy,Hy⟩:=e.xz; obtain ⟨C,hC,H⟩:=e.yz; let K:= min C (min Cx Cy); apply jitter s (P:=fun i d=>d≤pad (x i-y i)∧d≤ pad (x i-z i) ∧ d≤ pad (y i-z i)) (C:=K) (by unfold K; positivity); swap
  · refine Eventually.of_forall fun v D hd h p _=>?_ ; refine le_trans (Finset.sum_le_sum (fun w _=> le_of_eq (Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sound i _).le (sound ..).le) (sound ..).le)))) (chord hd (Real.one_le_sqrt.mpr hd) h.1 h.2.1 h.2.2 ⟨hi,fun _=> le_rfl⟩ ⟨hj,fun _=>le_rfl⟩ ⟨hk,fun _=>le_rfl⟩ he hv p)
  filter_upwards [Hx,Hy,H,s.good] with v hx hy h hi; unfold K; exact ⟨(div_le_iff₀ hi).2 ((min_le_right ..).trans ((min_le_left Cx Cy).trans (hx.trans_eq (mul_comm ..)))),(div_le_iff₀ hi).2 ((min_le_right ..).trans ((min_le_right Cx Cy).trans (hy.trans_eq (mul_comm ..)))),(div_le_iff₀ hi).2 ((min_le_left ..).trans (h.trans_eq (mul_comm ..)))⟩
include s in
lemma versatile (hi:i≤4)(hj:j≤4)(hk:k≤4)(he:4< i+j)(h:distFee L a (fun i=>x i-y i))(H:Beats S L a z): Dance S L a (i+j+k-4) (fun t w=>rate i (w-x t)*rate j (w-y t)*rate k (w-z t)):=by
  obtain ⟨C,hC,h⟩:=h; obtain ⟨D,hD,H⟩:= H; apply jitter s (P:=fun i J=>J≤pad (x i-y i)∧∀ w,S i w→ J≤pad (w-z i)) (C:=min C D) (by positivity); swap
  · refine Eventually.of_forall fun v B b hb p hp=>?_ ; have hh:0<B:=zero_lt_one.trans_le b; refine le_trans (Finset.sum_le_sum (fun w _=> le_of_eq (Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sound i _).le (sound ..).le) (sound ..).le)))) ((solo b (Real.one_le_sqrt.mpr b) hb.1 ⟨hi,fun _=> le_rfl⟩ ⟨hj,fun _=>le_rfl⟩ hk he p (fun w hw=> (half_lt_self hh).le.trans (hb.2 w (hp w hw)))).trans (by gcongr <;> norm_num))
  filter_upwards [h,H,s.good] with v hv hw ht; exact ⟨(div_le_iff₀ ht).2 ((min_le_left ..).trans (hv.trans_eq (mul_comm ..))),fun w h=> (div_le_iff₀ ht).2 ((min_le_right ..).trans ((hw w h).trans_eq (mul_comm ..)))⟩
include s in
lemma on_pitch (h:Beats S L a z)(hi:4< i): Dance S L a (i-4) (fun t w=> rate i (w-z t)):=by
  obtain ⟨C,hC,H⟩:=h; apply jitter s (P:=fun i D=> ∀ x,S i x→ D≤ pad (x-z i)) hC; filter_upwards [H,s.good] with i hi hh w hw; exact (div_le_iff₀ hh).2 ((hi w hw).trans_eq (mul_comm ..))
  refine Eventually.of_forall fun v D h H p hp=> ?_; have he:0<D:=zero_lt_one.trans_le h; refine le_trans (Finset.sum_le_sum (fun w _=> le_of_eq (Real.norm_of_nonneg (sound i _).le))) ((pc_out hi p he (fun w hw=> H w (hp w hw))).trans (le_trans ?_ (le_mul_of_one_le_right (by positivity) (Real.one_le_sqrt.mpr h)))) ; gcongr; norm_num
end YM.XSpace.Octave
