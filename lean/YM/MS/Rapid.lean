import YM.MS.Symbol

/-!
# One line carrying the Gaussian momentum gains
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real
open scoped ContDiff
variable {ι E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Scale
variable (S : Scale ι)
def strict (v : ι → Set E) : Cost ι E := ⟨v, fun i _ => S.basic i, fun i _ _ => S.one_le i⟩

def slow (v : ι → Set E) : Cost ι (E×F) := ⟨fun i => Prod.fst ⁻¹' v i, fun i p => S.full.cheap i p.2, fun i p _ => S.full.one_le i p.2 trivial⟩
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma pair_w (i) (p : E × F) : S.weight i p = max (S.weight i p.1) (S.weight i p.2) := by
  simp only [Scale.weight, Prod.norm_def, mul_max_of_nonneg _ _ (S.pos _).le]
  exact add_max ..
omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma slow_weight (v : ι → Set E) i (p : E×F) : S.full.cheap i p ≤ (S.slow v).cheap i p * S.weight i p.1 := by
  dsimp only [slow,full]; rw [S.pair_w i p,mul_assoc]
  refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) (S.basic_pos i).le
  exact le_mul_of_one_le_left (S.weight_pos i _).le (S.one_le_weight i _)
  exact le_mul_of_one_le_right (S.weight_pos i _).le (S.one_le_weight i _)
end Scale

variable {S : Scale ι} {v : ι → Set E}
def Line (S : Scale ι) (v : ι → Set E) (f : Kern ι E F) (g : ι→ℝ) :=
  ∀ b : ℕ, Costs (S.strict v) S f (fun i p => g i / S.weight i p^b)

def Rapid (S : Scale ι) (v : ι → Set E) (f : Kern ι (E×F) G) (g : ι→ℝ) :=
  ∀ b : ℕ, Costs (S.slow v) S f (fun i p => g i / S.weight i p.1^b)

variable {f : Kern ι E G} {g u : ι → ℝ}
lemma Line.rapid (h : Line S v f g) : Rapid S v (fun i (p : E×F) => f i p.1) g := by
  intro b
  refine Costs.linear (D:=S.slow v) (ContinuousLinearMap.fst ℝ E F) (h b) (fun _ _ hx=>hx) ?_
  exact ⟨1,by norm_num,1,fun i p _ => by
     simp [Scale.strict,Scale.slow,Scale.full]; exact le_mul_of_one_le_right (S.basic_pos i).le (S.one_le_weight i p.2)⟩
namespace Rapid
variable {r r' : Kern ι (E×F) G}
lemma smooth (h : Rapid S v r g) i : ContDiff ℝ ∞ (r i) := (h 0).smooth i
lemma nn (h : Rapid S v r g) : (S.slow (F:=F) v).NN fun i _=> g i := by simpa [Cost.NN] using (h 0).nonneg
lemma monotone (h : Rapid S v r g) (p : (S.slow (F:=F) v).Le (fun i _=>g i) (fun i _=> u i)) : Rapid S v r u :=
    fun b=> Costs.raise (h b) (by simp_rw [div_eq_mul_inv]; exact p.cancel (fun i q _=>inv_nonneg.mpr (pow_nonneg (S.weight_pos _ _).le _)))
lemma L (h : Rapid S v r g) (p : G →L[ℝ] H) : Rapid S v (fun i x=>p (r i x)) g := fun j => (h j).L p
lemma neg (h : Rapid S v r g) : Rapid S v (fun i x=> -r i x) g := fun j => (h j).neg
lemma add (h : Rapid S v r g) (p : Rapid S v r' g) : Rapid S v (fun i x=> r i x+r' i x) g := fun j => (h j).add (p j)
lemma sub (h : Rapid S v r g) (p : Rapid S v r' g) : Rapid S v (fun i x=> r i x-r' i x) g := fun j => (h j).sub (p j)
lemma cut (h : Rapid S v r g) {w : ι→ Set E} (ht : ∀ i, w i ⊆ v i) : Rapid S w r g := by
  refine fun b=> ⟨h.smooth, fun j=>?_⟩
  obtain ⟨C,hC,c,Hc⟩:= (h b).quoted j
  exact ⟨C,hC,c, fun i p hp => Hc i p (ht i hp)⟩
lemma fderiv (h : Rapid S v r g) : Rapid S v (fun i=> _root_.fderiv ℝ (r i)) (fun i => g i * S.length i) := by
  intro b
  refine ⟨fun i=> contDiff_infty_iff_fderiv.1 (h.smooth i) |>.2, fun j=>?_⟩
  refine ((h b).quoted (j+1)).right (fun i p _=> ?_)|>.left fun i p _=>le_of_eq (norm_iteratedFDeriv_fderiv)
  dsimp; simp only [div_eq_mul_inv]; ring_nf; rfl
private lemma permits {p : Kern ι (E×F) H} (P : Bound S p u) (j : ℕ) :
    ∃ b : ℕ, (S.slow (F:=F) v).Part S p (fun i x => u i * S.weight i x.1^b) j:= by
   have h i : 0 ≤ u i := P.nonneg i 0 (mem_univ _)
   obtain ⟨C,hC,b,hb⟩:= P.quoted j; refine ⟨b,C,hC,b, fun i x _=>?_⟩
   have hr:=h i; have hu:=S.pos i; have hw:=S.full.one_le i x trivial
   apply (hb i x trivial).trans
   calc
    _ ≤ C * ((S.slow v).cheap i x * S.weight i x.1)^b*(u i*S.length i^j) := by dsimp only; gcongr; exact S.slow_weight ..
    _ = _ := by rw [mul_pow]; ring

lemma bilinear {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {p : Kern ι (E×F) H} (B : G →L[ℝ] H →L[ℝ] A) (h : Rapid S v r g) (hp : Bound S p u) : Rapid S v (fun i x=> B (r i x) (p i x)) (fun i=> g i*u i) := by
  intro b
  refine ⟨fun i => B.isBoundedBilinearMap.contDiff.comp ((h.smooth i).prodMk (hp.smooth i)), fun j=>?_⟩
  let U(k:ℕ) i x := (j.choose k:ℝ)*‖iteratedFDeriv ℝ k (r i) x‖ * ‖iteratedFDeriv ℝ (j-k) (p i) x‖
  let W i (x:E×F):= g i*u i / S.weight i x.1^b * S.length i^j
  have hw : (S.slow v).NN W := by
     intro i x hx; have hz := h.nn i x hx; have ht:= hp.nonneg i x trivial; have hg:=S.weight_pos i x.1; have hi:= S.pos i; dsimp only at ht hz; unfold W; positivity
  have hr (k:ℕ) (hk:k ∈ Finset.range (j+1)) : (S.slow v).Le (U k) W := by
     obtain ⟨d,hd⟩:= permits (v:=v) hp (j-k)
     have hu := ((h (b+d)).quoted k).mul hd (fun _ _ _=> norm_nonneg _) (fun _ _ _=>norm_nonneg _)
     refine Cost.Le.left (Cost.Le.const_mul (Cost.Le.right hu (u:=W) (fun i x hx=>?_)) (j.choose k:ℝ) (by positivity) hw) fun i x hx=> (mul_assoc ..).le
     have hx:= S.weight_pos i x.1
     have hj : k≤j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
     apply le_of_eq; unfold W; conv_rhs => rhs; arg 2; rw [← Nat.add_sub_of_le hj];
     dsimp only; simp only [pow_add]; field_simp
  refine ((Cost.Le.finset_sum (Finset.range (j+1)) hr hw).const_mul ‖B‖ (norm_nonneg B) hw).left fun i x _ => B.norm_iteratedFDeriv_le_of_bilinear (h.smooth i) (hp.smooth i) x (by exact_mod_cast le_top)
lemma mul {a b : Kern ι (E×F) ℂ} (h : Rapid S v a g) (p : Bound S b u) :
    Rapid S v (fun i x=>a i x * b i x) (fun i=> g i*u i) := h.bilinear (ContinuousLinearMap.mul ℝ ℂ) p
end Rapid
end YM.MS
