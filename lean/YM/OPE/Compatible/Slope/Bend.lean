import YM.OPE.Compatible.Woven.Bough
/-! # Moment polynomials on undifferenced cover
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset
open scoped Topology BigOperators Classical
variable {I J:Type*}
abbrev Lieu (I:Type*):= I→ℝ
def tasting (l:List I)(x:Lieu I):ℝ:= (l.map x).prod
def Flavor (I:Type*)(d:ℕ):Submodule ℝ (Lieu I→ℝ):= Submodule.span ℝ {f | ∃ l:List I,l.length≤d ∧ f=tasting l}
lemma flavor_part (l:List I) (d:ℕ) (h:l.length≤ d): tasting l∈ Flavor I d:= Submodule.subset_span (show ∃ l':List I,l'.length≤d ∧ _ from ⟨l,h,rfl⟩)
lemma flavor_up {d h:ℕ}(hp:d ≤ h): Flavor I d ≤ Flavor I h:=by
   apply Submodule.span_mono; rintro i ⟨l,hl,hh⟩; exact ⟨l,hl.trans hp,hh⟩
lemma flavor_elim {d:ℕ} {f:Lieu I→ℝ}(h:f∈ Flavor I d)(P:(Lieu I→ℝ)→Prop) (hp:∀ l:List I, l.length ≤ d→ P (tasting l))(hz:P 0)(hd:∀ v w,v∈Flavor I d→w∈Flavor I d→ P v→ P w→ P (v+w))(hs:∀ (r:ℝ) v,v∈Flavor I d→P v→ P (r•v)): P f:=by
   refine Submodule.span_induction (p:=fun v _=>P v) ?_ hz hd hs h; rintro x ⟨l,hl,hx⟩; rw [hx]; exact hp _ hl
lemma flavor_prod {m n:ℕ}{f g:Lieu I→ℝ}(h:f∈ Flavor I m)(hp:g∈Flavor I n): f*g ∈ Flavor I (m+n):=by
   let U:=Flavor I (m+n)
   refine flavor_elim h (fun f=> f*g∈U) (fun i hi=>?_) (by rw [zero_mul]; exact U.zero_mem) (fun v w _ _ hv hw=>?_) (fun v w _ hw=>?_)
   · refine flavor_elim hp (fun g=> tasting i*g∈U) ?_ ?_ ?_ ?_
     · intro j hj; rw [show tasting i*tasting j=tasting (i++j) from funext fun x=>by simp [tasting]]; exact flavor_part _ _ (by simp only [List.length_append]; omega)
     · rw [mul_zero];exact U.zero_mem
     · intro v w _ _ a b; rw [mul_add]; exact U.add_mem a b
     intro v w _ a; rw [mul_smul_comm]; exact U.smul_mem _ a
   · rw [add_mul]; exact U.add_mem hv hw
   rw [smul_mul_assoc]; exact U.smul_mem _ hw
lemma flavor_one (d:ℕ): (1:Lieu I→ℝ)∈ Flavor I d:=flavor_part [] _ (Nat.zero_le _)
lemma flavor_cast (x:ℝ)(d:ℕ):(fun _:Lieu I=>x)∈Flavor I d:=by rw [show (fun _:Lieu I=>x)=x•1 from funext fun j=>by simp]; exact (Flavor I d).smul_mem _ (flavor_one d)
lemma flavor_position (x:I) : (fun p:Lieu I=> p x)∈ Flavor I 1:=by convert! flavor_part [x] 1 (by simp); simp [tasting]
lemma flavor_diagonal (u: Lieu J→ Lieu I)(h:∀ i,(fun x=> u x i) ∈ Flavor J 1){n:ℕ}{f:Lieu I→ℝ} (hp:f∈Flavor I n): f∘u ∈ Flavor J n:=by
    apply flavor_elim hp (fun f=> f∘u∈ Flavor J n) _ (by exact (Flavor J n).zero_mem) (fun _ _ _ _ a b=>(Flavor J n).add_mem a b) (fun _ _ _ a=>(Flavor J n).smul_mem _ a)
    intro l hl; apply flavor_up hl; clear hl; induction l with
    | nil=> exact flavor_one 0
    | cons i l ih=>
      rw [show tasting (i::l) ∘ u=(fun x=> u x i)*(tasting l ∘ u) from rfl,List.length_cons,add_comm]
      exact flavor_prod (h i) ih
-- support
variable [Fintype I]
def translit (x:Shift I):Lieu I:= fun i=> x i
lemma translate_bound (x:Shift I)(i:I): ‖translit x i‖ ≤ (size x:ℝ):=by
    unfold translit; rw [Real.norm_eq_abs,← Int.cast_abs]
    simp only [← Int.natCast_natAbs, Int.cast_natCast]; exact_mod_cast Finset.single_le_sum (f:=fun i=> (x i).natAbs) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)
lemma tasting_bill (l:List I)(x:Shift I): ‖tasting l (translit x)‖ ≤ (size x:ℝ)^l.length:=by
    induction l with
    | nil=>simp [tasting]
    | cons i l ih=>simp only [List.length_cons,pow_succ',tasting,List.map_cons,List.prod_cons,norm_mul]; exact mul_le_mul (translate_bound ..) ih (norm_nonneg _) (Nat.cast_nonneg _)
lemma tasting_cost {n:ℕ}{f:Lieu I→ℝ} (h:f∈ Flavor I n):∃ M:ℝ,0 ≤ M ∧ ∀ x:Shift I, ‖f (translit x)‖ ≤ M*poise n x:=by
    refine flavor_elim h (fun f=>∃ M:ℝ,0 ≤ M ∧ ∀ x:Shift I, ‖f (translit x)‖ ≤ M*poise n x) ?_ ?_ ?_ ?_
    · intro l hl; exact ⟨1,zero_le_one,fun x=>by
         rw [one_mul]; apply (tasting_bill ..).trans; have hh: (size x:ℝ) ≤ notch x:=by unfold notch;push_cast;linarith
         exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hh _).trans (pow_le_pow_right₀ (show 1 ≤ (notch x:ℝ) by exact_mod_cast notch_one x) hl)⟩
    · exact ⟨0,le_rfl,by simp⟩
    · rintro v w _ _ ⟨a,ha,hv⟩ ⟨b,hb,hw⟩; refine ⟨a+b,by linarith,fun x=>?_⟩; rw [Pi.add_apply]; linarith only [norm_add_le (v (translit x)) (w (translit x)), hv x,hw x]
    rintro v w _ ⟨b,hb,H⟩; refine ⟨‖v‖*b,by positivity,fun x=>?_⟩; rw [Pi.smul_apply,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H x) (norm_nonneg v)
end YM.OPE.Flume
