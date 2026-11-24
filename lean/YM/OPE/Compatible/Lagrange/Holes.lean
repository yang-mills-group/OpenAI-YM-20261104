import YM.OPE.Compatible.Lagrange.Green
/-! Choose a centered arithmetic subgrid along even when finitely many points prohibited -/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Filter Metric Polynomial Finset
open scoped BigOperators Topology
variable {x δ R:ℝ}{k n:ℕ}
-- shift added to absolute x. points exactly multiples of g
lemma disjoint_grid {s:Finset ℝ}(hk:s.card < k) (h:0<δ)(x:ℝ): ∃ b:ℝ, 0 < b ∧ b ≤ (k:ℝ)*δ ∧ ∀ i:ℤ,
    ((i:ℝ)*(2*(k:ℝ)*δ)+b)∉s ∧ ∃ a:ℤ,(i:ℝ)*(2*(k:ℝ)*δ)+b+x = (a:ℝ)*δ:=by
   have hp(j:Fin k): 0 ≤ (j.val:ℝ) ∧ (j.val:ℝ)+1 ≤ k := ⟨by positivity,by exact_mod_cast j.isLt⟩
   have hh : (0:ℝ) < k:=by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hk
   let n:= ⌊x/δ⌋; let b(j:Fin k):=(↑(n+1+j.val):ℝ)*δ-x; have he(j:Fin k):0 < b j ∧ b j ≤ (k:ℝ)*δ:=by
       have h1 : x/δ < (n:ℝ)+1:=Int.lt_floor_add_one _; have h₂:(n:ℝ) ≤ x/δ:=Int.floor_le _
       unfold b; push_cast; obtain ⟨ha,hw⟩:=hp j; constructor <;> nlinarith only [(le_div_iff₀ h).1 h₂,(div_lt_iff₀ h).1 h1,h,ha, hw]
   let t(i:ℤ)(j:Fin k):ℝ:= i*(2*(k:ℝ)*δ)+b j; have hb : ∃ i:Fin k,∀ j,t j i∉s :=by
       by_contra! hn; choose f hf using hn; obtain ⟨i,_,j,_,hv,hv'⟩:=exists_ne_map_eq_of_card_lt_of_maps_to (show s.card < (@univ (Fin k) _).card from by simpa using hk) (fun j _=> hf j)
       -- map ambiguity
       have he': f i=f j:=by
           rcases lt_trichotomy (f i) (f j) with hF|hF|hF
           · have hi : (f i:ℝ)+1 ≤ f j:=by exact_mod_cast hF; -- linarith
             unfold t at hv'; exfalso
             have hL:= mul_le_mul_of_nonneg_right hi (show 0 ≤ 2*(k:ℝ)*δ by positivity); nlinarith only [hL,(he i).2,(he j).1,hv',mul_pos hh h]
           · exact hF
           have hi: (f j:ℝ)+1 ≤ f i:=by exact_mod_cast hF
           unfold t at hv'; exfalso; have hL:= mul_le_mul_of_nonneg_right hi (show 0 ≤ 2*(k:ℝ)*δ by positivity); nlinarith only [hL,(he j).2,(he i).1,hv',mul_pos hh h]
       apply hv; unfold t at hv'; rw [he'] at hv'; unfold b at hv'; apply Fin.ext; exact_mod_cast add_left_cancel ((Int.cast_injective (α:=ℝ)) (mul_right_cancel₀ h.ne' (sub_left_inj.mp (add_left_cancel hv')))) -- cancel sub names
   obtain ⟨j,hj⟩:=hb
   refine ⟨b j,(he j).1,(he j).2,fun i=> ⟨hj i,i*(2*(k:ℤ))+(n+1+(j.val:ℤ)),?_⟩⟩; unfold b; push_cast; ring
end YM.FrameRead
