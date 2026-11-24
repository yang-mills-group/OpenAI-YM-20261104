import YM.FormalBulk08.Gorge.Ore

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Gorge
open Lava Function
open scoped BigOperators ENNReal Classical
variable {V I : Type*} (D : Reach V) {σ : ℝ} {r : ℕ}
lemma wide_turn (v : chain V r) (s : Equiv.Perm (Fin r)) : wide D (v ∘ s)=wide D v := by
   have h (v : chain V r) (s : Equiv.Perm (Fin r)) : wide D (v ∘ s) ≤ wide D v := known_wide _ _ _ (fun i j=> reached D v (s i) (s j))
   exact le_antisymm (h v s) (by simpa [Function.comp_assoc] using h (v ∘ s) s.symm)

variable {D}
lemma Bail.spins {T : Tile V r} {C : ℝ} (h : Bail D σ T C) (s : Equiv.Perm (Fin r)) : Bail D σ (fun v=> T (v ∘ s)) C := by
   refine ⟨h.1,fun i a=>?_⟩
   let g : pack i a → pack (s.symm i) a := fun x=> ⟨x.val ∘ s,by simp [x.property]⟩
   refine le_trans ?_ (h.2 (s.symm i) a); calc
      _ = ∑' x:pack i a, glitter D σ T (g x).val := tsum_congr fun x=>by change _=shine _ (wide D (x.val ∘ s))*_; rw [wide_turn]; rfl
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (show Injective g from fun x y e=> Subtype.ext (funext fun j=>by have he := congr_fun (congr_arg Subtype.val e) (s.symm j);simpa [g] using he)) _
lemma Bail.smooth {T : Tile V r} {C : ℝ} (h : Bail D σ T C) : Bail D σ (sand T) C := by
   let β:= Equiv.Perm (Fin r); let n : ℝ := Fintype.card β
   have hn : 0<n:= by unfold n; change (0:ℝ)< Fintype.card (Equiv.Perm (Fin r)); positivity
   let U (s : Equiv.Perm (Fin r)) : Tile V r:= fun v=>T (v ∘ s)
   have hx : sand T=∑ s,n⁻¹ • U s:= by funext v; simp only [sand,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,U];rw [←Finset.mul_sum,mul_comm, div_eq_mul_inv]
   rw [hx]; apply (bail_many Finset.univ _ _ (fun s _=>(h.spins s).smul n⁻¹)).mono; simp only [Finset.sum_const,abs_of_pos (inv_pos.mpr hn), nsmul_eq_mul,Finset.card_univ];change n*(_*C)≤ C; rw [←mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
lemma Bail.lengthen {T : Tile V r} {C : ℝ} (h : Bail D σ T C) {m : ℕ} (e : r=m) : Bail D σ (Lava.lengthen e T) C := by cases e; exact h
lemma Bail.pier {R : Reach I} {D : Reach V} (g : I → V) (he : Injective g) (hw : ∀ v w, R.d v w ≤ D.d (g v) (g w))
   {T : Tile V r} {C : ℝ} (hs : 0 ≤ σ) (h : Bail D σ T C) : Bail R σ (jetty g T) C := by
   refine ⟨h.1,fun i a=>?_⟩
   let t : pack i a→pack i (g a) := fun x=> ⟨g ∘ x.val,by simp [x.property]⟩
   have ht : Injective t:= fun x y e=>Subtype.ext (funext fun j=> he (congr_fun (congr_arg Subtype.val e) j))
   refine (ENNReal.tsum_le_tsum (g:=fun x=>glitter D σ T (t x).val) fun x=>?_).trans ((ENNReal.tsum_comp_le_tsum_of_injective ht (fun x=>glitter D σ T x.val)).trans (h.2 _ _))
   unfold glitter; exact mul_le_mul_left (shine_le _ hs (known_wide _ _ _ (fun j k=>(hw _ _).trans (reached D (t x).val j k)))) _

lemma glitter_sum_usable {T : Tile V r} {C : ℝ} (h : Bail D σ T C) (hs : 0≤σ) (i : Fin r) (a : V) : Summable fun v : pack i a=> T v.val := by
   refine ((tsum_enorm_ne_top_iff_summable_norm).mp (lt_top_iff_ne_top.mp ?_)).of_norm
   refine lt_of_le_of_lt ?_ (lt_of_le_of_lt ((h.shrink hs).2 i a) ENNReal.ofReal_lt_top); simp only [glitter,shine_one,one_mul,le_refl]

lemma from_evil {f : I→ℝ} {C : ℝ} (hp : 0≤C) (h : ∀ i,0≤ f i) (e : (∑' i,ENNReal.ofReal (f i)) ≤ ENNReal.ofReal C) : Summable f ∧ ∑' i,f i ≤ C := by
   have he := ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top e)
   simp_rw [ENNReal.toReal_ofReal (h _)] at he; rw [←ENNReal.ofReal_tsum_of_nonneg h he, ENNReal.ofReal_le_ofReal_iff hp] at e; exact ⟨he,e⟩
lemma Bail.measured {T : Tile V r} {C : ℝ} (h : Bail D σ T C) (i : Fin r) (a : V) :
    Summable (fun v : pack i a => Real.exp (σ * wide D v.val)*‖T v.val‖) ∧ ∑' v : pack i a, Real.exp (σ * wide D v.val)*‖T v.val‖ ≤ C := by
   apply from_evil h.1 (fun _=>by positivity); simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm]; apply h.2
end YM.FormalBulk08.Gorge
