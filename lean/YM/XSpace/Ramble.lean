import YM.XSpace.Chordal
/-!
# Chiral cluster distant-probe, signed and absolute parts
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Set Filter Lattice Trace Relief Sail Drama
open scoped Topology BigOperators
variable {x y z w u v:Cover}{p D₀:ℝ}{A B C:Toe}
def sheer (D:ℝ)(x z:Cover)(A:Toe)(w:Cover):= (1-veil D (w-z))*A (w-z)-A (x-z)
lemma shear (h:A∈Terrain 4) :∃ C:ℝ,0<C∧∀ (x z w:Cover), ‖sheer (pad (x-z)) x z A w‖≤ C* rate 5 (x-z)*pad (w-x):=by
  obtain ⟨C,hC,H⟩:= in_flight A h; obtain ⟨D,hD,J⟩:= supply A h; refine ⟨max C (D*4),lt_of_lt_of_le hC (le_max_left ..),fun x z w=>?_⟩; let d:= pad (x-z); let u:=w-z; have hx:0<d:=included _; let b:= w-x; by_cases hp:pad b≤ d/2
  · have hb:veil d u=0:=by_contra fun h=>by
      have hh:=paved hx h; have hk := trio x z w; rw [sym x w,sym z w] at hk; change d≤pad b+pad u at hk; linarith
    unfold sheer; rw [hb,sub_zero,one_mul,show w-z=(x-z)+b by unfold b;abel]; apply (H (x-z) b hp).trans; rw [mul_right_comm C]; change C* _ *pad b≤ _ * pad b; have ht:0<pad b:=included b; gcongr; · exact (sound ..).le
    apply le_max_left
  have hb:= lt_of_not_ge hp; change ‖_ - A _‖ ≤ _; have he(v:Cover)(h:d/8≤pad v): ‖A v‖≤D*rate 4 (x-z):=J v d hx h
  have ht: ‖(1-veil d u)*A u‖≤ D*rate 4 (x-z):= by
    by_cases hk:veil d u=1; rw [hk,sub_self,zero_mul,norm_zero]; exact mul_nonneg hD.le (sound ..).le
    rw [norm_mul,Real.norm_of_nonneg (sub_nonneg.mpr (dive ..))]; exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [crest d u])).trans (he _ (in_void hx hk).le)
  apply (norm_sub_le _ _).trans ((add_le_add ht (he (x-z) (by change d/8≤d; linarith))).trans ?_); have ht:0<pad (w-x):=included _; calc
   _ = D*4 * rate 5 (x-z)*(d/2):=by simp_rw [rated]; have hz:0<pad (x-z):=hx; unfold d; field_simp; ring
   _ ≤ _:= mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right ..) (sound ..).le) hb.le (by positivity) (mul_nonneg (le_trans hC.le (le_max_left ..)) (sound ..).le)
abbrev string (A B:Toe)(x y:Cover): Toe:= fun w=> A (w-x)* B (w-y)
abbrev res (A B: Toe)(x y:Cover):= ∑' w:Cover,string A B x y w
def pitch (B C:Toe)(x y z:Cover): Toe:=fun w=>veil (pad (x-z)) (w-z)*string B C x y w
lemma in_pocket (h:32*pad (x-y)≤pad (x-z))(hx:pad (w-z)≤pad (x-z)/3): pad (x-z)/8≤pad (w-x)∧pad (x-z)/8≤pad (w-y):=by
  have ht:= trio x z w; rw [sym x w,sym z w] at ht; have hh:= trio w x y
  have h':0<pad (x-z):=included _; constructor <;> linarith
lemma shipping (h:B∈Terrain 3)(K:C∈Terrain 3)(a:Axis): ∃ D:ℝ,0<D ∧ ∀ (x y z w:Cover), 32* pad (x-y) ≤ pad (x-z) → η a (pitch B C x y z) w≠0 → pad (w-z) ≤ pad (x-z) ∧ ‖η a (pitch B C x y z) w‖ ≤ D * rate 7 (x-z):=by
  let b:= mov (-step a) B; let c:=mov (-step a) C; obtain ⟨M,hM,H⟩:=supply B h; obtain ⟨N,hN,J⟩:= supply C K; obtain ⟨E,hE,L⟩:= supply c (slide_hill K _); obtain ⟨T,hT,Q⟩:= supply (η a B) (down_hill h _); obtain ⟨U,hU,G⟩:= supply (η a C) (down_hill K _); refine ⟨16*M*N+(T*E+M*U),by positivity,fun x y z w Hx Hp=>?_⟩; let v:=w-step a; let B' t:=B (t-x); let C' t:=C (t-y); let D':=pad (x-z); let u t:=veil D' (t-z); let X:= η a (pitch B C x y z) w; have he: X=(u v-u w)*(B' w*C' w)+ u v*((B' v-B' w)* C' v+B' w*(C' v-C' w)):=by change u v*(B' v*C' v)-u w*(B' w*C' w)=_; ring
  have hh:0<D':=included _; have hk:32≤D':=by dsimp [D']; linarith [room (x-y)]
  have hz:pad (w-z)≤ D'/3:=by
    by_cases hp:u w=0
    · have hv:u v≠0:=fun ht=>Hp (by change X=0; rw [he,hp,ht]; ring)
      have h:=paved hh hv; unfold v at h; rw [sub_right_comm w] at h; linarith [edge_low (w-z) a]
    linarith [paved hh (x:=w-z) hp]
  refine ⟨le_trans hz ?_,?_⟩; · change D'/3≤D'; linarith
  obtain ⟨h1,h2⟩:=in_pocket Hx hz; have hp:‖u v-u w‖≤16 *D'⁻¹:=by change ‖veil D' (v-z)-_‖≤_; unfold v; rw [sub_right_comm w]; exact (lace_step hh (w-z) a).trans_eq (div_eq_mul_inv ..)
  have hu : ‖u v‖≤1:= by rw [Real.norm_of_nonneg (crest ..)]; exact dive ..
  have h3:‖B' v-B' w‖≤ T*D'⁻¹^4:=by change ‖B (_-_)-_‖≤_; unfold v; rw [sub_right_comm w]; exact Q _ _ hh h1
  have h4:‖C' v-C' w‖≤U* D'⁻¹^4:=by change ‖C (_-_)-_‖ ≤_; unfold v; rw [sub_right_comm w]; exact G _ _ hh h2
  have h5:‖B' w‖≤ M * D'⁻¹^3:= H _ _ hh h1; have h6:‖C' w‖≤ N* D'⁻¹^3:=J _ _ hh h2; have h7:‖C' v‖≤ E*D'⁻¹^3:=by convert L (w-y) D' hh h2 using 2; change C (w-step a-y)=C (-step a+(w-y)); congr 1; abel
  change ‖X‖≤_; rw [he]; refine (norm_add_le ..).trans (add_le_add (b:=16* D'⁻¹*(M*D'⁻¹^3*(N*D'⁻¹^3))) (d:=T*D'⁻¹^4*(E*D'⁻¹^3)+(M*D'⁻¹^3)*(U*D'⁻¹^4)) ?_ ?_ |>.trans_eq ?_); swap
  · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans ((norm_add_le ..).trans (add_le_add (by rw [norm_mul]; exact mul_le_mul h3 h7 (norm_nonneg _) (by positivity)) (by rw [norm_mul]; exact mul_le_mul h5 h4 (norm_nonneg _) (by positivity)))) -- infer?
  · simp_rw [norm_mul]; exact mul_le_mul hp (mul_le_mul h5 h6 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
  rw [rated]; unfold D'; ring
end YM.XSpace.Octave
