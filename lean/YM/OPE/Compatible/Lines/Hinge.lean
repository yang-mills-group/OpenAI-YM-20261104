import YM.OPE.Compatible.Lines.Groove
/-!
# variable displacement relative geometry. Deterministic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice
open scoped Topology BigOperators Classical
variable {X:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){Q:Finset X}
variable (H:Crown Q){s:X→ℝ}{g:Sight}(x:X→ E4){f:Wing D Q→ℝ}
set_option quotPrecheck false
local notation "p" => fun (j:Wing D Q)=>s (par D j.1.1)
-- exactly one moves
def flex (D:Origin X)(Q:Finset X)(i:Wing D Q)(u v:X):Prop:= ¬ (inMotion D Q i u ↔ inMotion D Q i v)
lemma later {i:Wing D Q}{u v w:X}(hu:v≤u)(hv:v≤w)(hf:flex D Q i u w) : v ≤ par D i.1.1 :=by
   apply touch_par; by_cases hh: inMotion D Q i u
   · apply lt_of_le_not_ge; exact ((D.path hu hh).resolve_right (fun h=>hf (iff_of_true hh (h.trans hv)))); exact fun h=>hf (iff_of_true hh (h.trans hv))
   have hl : inMotion D Q i w := Classical.byContradiction fun h=>hf (iff_of_false hh h); apply lt_of_le_not_ge; exact ((D.path hv hl).resolve_right fun h=> hh (h.trans hu)); exact fun h=> hh (h.trans hu)
variable {M η ρ t A L:ℝ}
lemma shift_budget (h:∀ i:Wing D Q,0 ≤ p i)(hf:∀ i,|f i| ≤ ρ)(hr:0≤ρ)(hL:∀ i,‖FrameRead.trail (g.code i)‖≤L)(hh:0≤L) {u v:X} (ht:0≤t)(hu:∀ i, flex D Q i u v → p i ≤ t) :
   ‖displacement D Q s g f u-displacement D Q s g f v‖ ≤ ↑(Fintype.card (Wing D Q))*(L*ρ)*t:=by
   unfold displacement; rw [← Finset.sum_sub_distrib]; refine (norm_sum_le ..).trans ?_; rw [mul_assoc,mul_assoc,← nsmul_eq_mul,← Finset.card_univ,← Finset.sum_const]; refine Finset.sum_le_sum fun i _=>?_ ; split <;> rename_i he
   · split <;> rename_i hv; simp only [sub_self,norm_zero]; positivity
     have hz:=hu i (fun f=> hv (f.mp he)); simp only [sub_zero,norm_smul,Real.norm_eq_abs,abs_mul, abs_of_nonneg (h i)]; rw [mul_comm L]; exact mul_le_mul (mul_le_mul (hf i) hz (h i) hr) (hL _) (norm_nonneg _) (mul_nonneg hr ht)
   split <;> rename_i hv
   · have hz:= hu i (fun f=>he (f.mpr hv)); simp only [zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (h i)]; rw [mul_comm L]; exact mul_le_mul (mul_le_mul (hf i) hz (h i) hr) (hL _) (norm_nonneg _) (mul_nonneg hr ht)
   simp only [sub_zero,norm_zero]; positivity
-- allUp positions lengths admissibility
structure Bright (Q:Finset X)(s:X→ℝ) : Prop where
   pos i : i∈Q→ 0<s i
   range' i j : i≤j→ j∈Q→ s j≤ s i
variable (hp:Bright Q s)
include H hp
lemma dim_order (j:Wing D Q): 0 < p j:= hp.pos _ (par_leg _ _ H ((Finset.mem_erase.mp j.fst.2).2))
lemma dim_forks {i:Wing D Q}{u v w:X} (hu:v≤u)(hv:v≤w)(hf:flex D Q i u w) : p i ≤ s v:=hp.range' _ _ (later D hu hv hf) (par_leg _ _ H ((Finset.mem_erase.mp i.1.2).2))
lemma perturb (hf:∀ i,|f i| ≤ ρ)(hr:0≤ρ)(hL:∀ i,‖FrameRead.trail (g.code i)‖≤ L)(hh:0≤L)
    (hv: Ridge s η M D Q x) (hb: (Fintype.card (Wing D Q):ℝ)*L*ρ ≤ min 1 (η/2)) : Ridge s (η/2) (M+1) D Q (reload D Q s g x f):=by
   let Y:=displacement D Q s g f
   have ht (u v w:X)(hi:w ∈ Q)(hu:w ≤ u)(hw:w ≤ v): ‖Y u-Y v‖ ≤ min 1 (η/2)*s w:=by
        have hz:= hp.pos _ hi; have hq := shift_budget (f:=f) D (fun i=>(dim_order D H hp i).le) hf hr hL hh hz.le (fun i f=> dim_forks D H hp hu hw f); rw [← mul_assoc (↑(Fintype.card (Wing D Q)):ℝ)] at hq; exact hq.trans (mul_le_mul_of_nonneg_right hb hz.le)
   have he (u v:X): reload D Q s g x f u - reload D Q s g x f v=x u-x v+(Y u-Y v):=by unfold reload Y; abel
   refine ⟨(belly ..).trans hv.belly,fun u v hu hw hl=>?_,fun u v hi hj hh hz=>?_⟩
   · rw [he]; apply (norm_add_le ..).trans; apply le_trans (add_le_add (hv.near u v hu hw hl) (ht u v u hu le_rfl hl)); rw [← add_mul]; exact mul_le_mul_of_nonneg_right (add_le_add_right (min_le_left 1 _ ) _) (hp.pos u hu).le -- names
   rw [he]; let w:= couple D u v; have hh':= hv.span _ _ hi hj hh hz; have hw:= diverge D H hi hh; have ht :=ht _ _ w hw (coupled_left ..) (coupled_right ..); have hd:=ht.trans (mul_le_mul_of_nonneg_right (min_le_right ..) (hp.pos w hw).le)
   let x':= x u - x v; let y:=Y u-Y v; change ‖y‖ ≤ _ at hd; have hr: ‖x'‖ ≤ ‖x'+y‖+‖y‖:= (norm_sub_le (x'+y) y)|>.trans (le_refl _) |> fun h=> by simpa using h
   change η/2*s w ≤ _; change _ ≤ ‖x'‖ at hh'; change η*s w≤_ at hh'; change _ ≤ ‖x'+y‖; linarith
end YM.OPE.Arboreal.Trace
