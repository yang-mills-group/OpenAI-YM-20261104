import YM.XSpace.Ballad
/-!
# Probe local cutoff for the large R cost
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Set Filter Lattice Trace Relief Sail Drama Litter
open scoped Topology BigOperators
variable {x y z w u v:Cover}{p D:ℝ}{A:Toe}
def veil (D:ℝ)(x:Cover):= min 1 (max 0 (2-8*pad x / D))
lemma crest (D:ℝ)(x:Cover): 0≤veil D x:= le_min zero_le_one (le_max_left ..)
lemma dive (D:ℝ)(x:Cover): veil D x≤1:=min_le_left ..
lemma paved (hd:0<D)(h: veil D x≠0) : pad x < D/4 :=by
  by_contra! hv; apply h; unfold veil; rw [max_eq_left (?_ : 2-8*pad x/D≤0), min_eq_right zero_le_one]; rw [sub_nonpos]; apply (le_div_iff₀ hd).2; linarith
lemma in_void (hd:0<D)(h:veil D x≠1): D/8<pad x:=by
  by_contra! hv; apply h; unfold veil; apply min_eq_left; apply le_max_of_le_right; rw [le_sub_iff_add_le]; apply add_le_of_le_sub_left; apply (div_le_iff₀ hd).2; linarith
private lemma crown {a b C:ℝ}(hc:0≤C)(h:b≤a+C): min 1 (max 0 b) ≤ min 1 (max 0 a)+C:=by
  by_cases he:1≤max 0 a
  · rw [min_eq_left he]; exact (min_le_left ..).trans (le_add_of_nonneg_right hc)
  rw [min_eq_right (le_of_not_ge he)]; apply le_trans (min_le_right ..); exact max_le (by positivity) (h.trans (add_le_add (le_max_right ..) le_rfl)) -- max positivity?
lemma lace (hd:0<D)(p:ℝ)(hp:0≤p) (h:pad y≤pad x+p): veil D x ≤ veil D y +8*p / D:=by
  refine crown (by positivity) ?_; field_simp; linarith
lemma pad_step (i:Axis): pad (Lattice.step i) ≤ 2:=by unfold pad area; have h:reach (step i) ≤1:= Finset.sup_le (fun x (_:x∈(Finset.univ:Finset Axis))=> by simp only [Lattice.step_apply]; split <;> simp); exact_mod_cast (show 1+reach (step i)≤2 from by omega)
lemma edge_low (u:Cover)(a:Axis): pad u-2 ≤ pad (u-step a):= by have h:= triad (u-step a) (step a); rw [sub_add_cancel] at h; linarith [pad_step a]
lemma edge_high (u:Cover)(a:Axis):pad (u-step a) ≤ pad u+2:= by rw [sub_eq_add_neg]; exact (triad ..).trans (add_le_add le_rfl (flip_pad (step a) ▸ pad_step a)) -- eq?
lemma lace_step (hd:0<D)(x:Cover)(a:Axis): ‖η a (veil D) x‖ ≤16 / D:=by
  change |veil D (x-step a)-veil D x|≤ 16 / D; rw [abs_le]; have h:= lace hd 2 (by norm_num) (edge_high x a); have hh:= lace hd 2 (by norm_num) (show pad x≤pad (x-step a)+2 by linarith [edge_low x a]); constructor <;> linarith
lemma supply {k:ℕ}(A:Toe)(h:A∈Terrain k) :∃ C:ℝ,0<C∧∀ (x:Cover)(D:ℝ), 0<D→ D/8≤pad x→ ‖A x‖≤ C*D⁻¹^k:=by
  obtain ⟨C,hC,H⟩:= sonar h; refine ⟨C*8^k,by positivity,fun x D hD hx=>?_⟩; exact (H x).trans ((mul_le_mul_of_nonneg_left (moon_le (by positivity :0<D/8) hx) hC.le).trans_eq (by rw [inv_div,div_eq_mul_inv,mul_pow]; ring))
open Next.Rank.Beamer
lemma in_flight (A:Toe)(h:A∈Terrain 4): ∃ C:ℝ,0<C∧∀ (x u:Cover),pad u≤pad x/2→ ‖A (x+u)-A x‖ ≤ C* pad u*rate 5 x:=by
  classical
  choose B hB H using fun i:Axis=> supply (Relief.D i A) (steps_hill h i); set C:= ∑ i:Axis, B i; have hC :0<C:= Finset.sum_pos (fun i _=> hB i) Finset.univ_nonempty; refine ⟨C*4,by positivity,fun x u hu=>?_⟩; let L:= pad x; have hl:0<L:=included _; let D:= C*rate 5 x
  have he (v:Cover)(i:Axis)(hf:pad v≤L/2): ‖A (x+v+step i)-A (x+v)‖≤ D:=by
    have hx:L/8≤pad (x+v):= by have hh:= triad (x+v) (-v); rw [add_neg_cancel_right,flip_pad] at hh; change L≤_ at hh; linarith
    refine (H i _ _ hl hx).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i (_:i∈Finset.univ)=> (hB i).le) (Finset.mem_univ i)) (by positivity))
  have head (n:ℕ)(u:Cover)(p:street u=n)(hp:pad u≤L/2): ‖A (x+u)-A x‖ ≤ n * D:=by
    induction n generalizing u with
    | zero=> obtain h|⟨z,hz,_⟩:= past_stepping u; · simp [h];
             omega
    | succ n ih=>
      obtain h|⟨z,hz,hg,i,H⟩:= past_stepping u; · rw [h]; simp; apply mul_nonneg (by positivity) (mul_nonneg hC.le (sound ..).le)
      have h₀:pad z≤ pad u:= add_le_add le_rfl (Nat.cast_le.mpr hg); have h' : ‖A (x+u)-A (x+z)‖ ≤ D:=by cases H with | inl h=> rw [h,← add_assoc]; exact he z i (h₀.trans hp) | inr h=> rw [h,← add_assoc, norm_sub_rev]; exact he u i hp
      apply (norm_sub_le_norm_sub_add_norm_sub _ _ (A x)).trans ((add_le_add h' (ih z (by omega) (h₀.trans hp))).trans_eq ?_); push_cast; ring
  apply (head _ u rfl hu).trans; unfold D; unfold pad Drama.area; have ht: (↑(street u):ℝ)≤4*(reach u):=by exact_mod_cast street_price u
  set V:= rate 5 x; have hv:0<V:=sound ..; calc
    _ ≤ (4*(reach u:ℝ))*(C*V):=by gcongr
    _ ≤ _:=by rw [← sub_nonneg]; ring_nf; positivity
end YM.XSpace.Octave
