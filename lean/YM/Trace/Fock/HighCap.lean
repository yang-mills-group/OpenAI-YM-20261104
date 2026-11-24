import YM.Trace.Fock.Foot
noncomputable section
set_option maxHeartbeats 600000
set_option autoImplicit false
namespace YM.Trace.Shell
open Filter Function MeasureTheory Set Measure YM Boundary Complex
open scoped Pointwise BigOperators Topology ENNReal
variable {q n m : ℕ}
lemma foot_other (i : Fin (n+1)) (x:Cords (n+1)) : join i (0,i.removeNth x)= update x i 0 := by
     rw [join_eq]
     funext j
     by_cases h:j=i; · subst j; rw [update_self,Fin.insertNth_apply_same]
     obtain ⟨r,rfl⟩ := Fin.exists_succAbove_eq_iff.mpr h
     rw [update_of_ne h]; exact Fin.insertNth_apply_succAbove (α:=fun _:Fin (n+1)=>Mom) ..
def beamDegree (i : chartIdx q n) : ℕ := ∑ j, (momentDegree (i j)-1)
def capOne (c : chartIdx q n→ℂ) (i : Fin n) (σ : chartIdx q n) := if momentDegree (σ i)=0 then 0 else c σ
abbrev highCap (c : chartIdx q n→ℂ) := ∀ σ, ∀ i:Fin n, momentDegree (σ i)=0 → c σ=0
def dividedSlot (i : momentSlot q) (p : Mom) : ℂ := momentEntry i p / ‖p‖
def release (c : chartIdx q n→ℂ) (x:Cords n) := ∑ i, c i * ∏ l, dividedSlot (i l) (x l)
lemma entry0 (a : momentSlot q) (p:Mom) : momentEntry a 0=(if momentDegree a=0 then momentEntry a p else 0) := by
 by_cases h:momentDegree a=0
 · simpa [h] using momentEntry_smul 0 (le_refl 0) a p
 simpa [if_neg h,zero_pow h] using momentEntry_smul 0 (le_refl 0) a p -- reference h unavailable in simp pos
lemma entry0' (x:Cords n) (χ : chartIdx q n) (i : Fin n) (j) : momentEntry (χ j) (update x i 0 j) = (if j=i ∧ momentDegree (χ i) ≠0 then 0 else momentEntry (χ j) (x j)) := by
 by_cases hj:j=i
 · subst j; rw [update_self,entry0 (χ i) (x i)]; split_ifs <;> tauto
 simp [hj]
private lemma high_one (c : chartIdx q n→ℂ) (x) (j : Fin n) : chartValue (capOne c j) x = chartValue c x - chartValue c (update x j 0) := by
 unfold chartValue; rw [← Finset.sum_sub_distrib]; congr! 1 with χ hχ
 rw [← mul_sub]
 by_cases h:momentDegree (χ j)=0
 · rw [Finset.prod_congr (g:=fun l=> momentEntry (χ l) (x l)) rfl (fun l _=>show _ = _ from Eq.trans (entry0' x χ j l) (by simp [h]))]
   simp [capOne,h]
 have h0 := Finset.prod_eq_zero (Finset.mem_univ j) (f:=fun i=>momentEntry (χ i) (update x j 0 i)) (by rw [entry0']; simp [h])
 simp [capOne,h,h0]
private lemma high_clean (c : chartIdx q n→ℂ) (hsz : ∀ i, ∀ x:Cords n, chartValue c (update x i 0)=0) : ∃ c':chartIdx q n→ℂ, chartValue c=chartValue c' ∧ highCap c' := by
  suffices hi : ∀ s:Finset (Fin n), ∃ c', chartValue c'=chartValue c ∧ ∀ σ, ∀ i∈s, momentDegree (σ i)=0 → c' σ=0 by
     obtain ⟨c',hc,h⟩:=hi Finset.univ; exact ⟨c',hc.symm,fun t i=> h t i (by simp)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨c,rfl,fun i j hj=>by simp only [Finset.notMem_empty] at hj⟩
  | insert j s hi I =>
       obtain ⟨c',hc,h⟩:= I
       refine ⟨capOne c' j, funext (fun x=> (high_one _ x _).trans (by rw [hc,hsz,sub_zero])), fun t i hi ht=> ?_⟩
       rcases Finset.mem_insert.mp hi with e|e; · subst i; rw [capOne,if_pos ht]
       rw [capOne, h t i e ht]; split <;> rfl'
lemma release_mill (c : chartIdx q n→ℂ) (x:Cords n) (hx : ∀ i, x i ≠ 0) : release c x*(mill x : ℂ) = chartValue c x := by
     unfold chartValue release mill; push_cast; rw [Finset.sum_mul]
     have h i : (‖x i‖:ℂ)≠0 := by norm_cast; simpa using hx i
     congr! 1 with σ; rw [mul_assoc,← Finset.prod_mul_distrib]; congr! 2 with i
     unfold dividedSlot; field_simp [h i]
lemma ν_positive (x : Mom) : ν {x}=0 := MeasureTheory.withDensity_absolutelyContinuous _ _ (measure_singleton _)
lemma coord_dense (n) : ∀ᵐ x:Cords (n+1)∂νpow (n+1), ∀ i, x i≠0 := by
 refine ae_all_iff.mpr (fun i=>ae_iff.mpr ?_)
 suffices (join i ⁻¹' {x | ¬ x i ≠ 0}:Set (Mom×Cords n)) = {(0:Mom)}×ˢ univ by
      rw [← (join_preserving i).measure_preimage_emb (join i|>.measurableEmbedding), this, Measure.prod_prod, ν_positive, zero_mul]
 ext x; simp only [mem_preimage,mem_setOf_eq, join_pos, not_not,mem_prod, mem_univ,mem_singleton_iff,and_true]
lemma mill_pos {x:Cords n} (h : ∀ i, x i≠0) : 0 < mill x := Finset.prod_pos (fun i _=> norm_pos_iff.mpr (h _))
lemma release_on_frame {v : Test4→L[ℂ] Sum m} (k : @Angle m (n+1)) (x:Cords (n+1)) (hx : mill x≠0) (c : chartIdx q (n+1)→ℂ) (he : smoothBody v k x=chartValue c x) : fullWave v (n+1) x k=release c x := by
     have h : ∀ i, x i ≠0 := fun i hi=>hx (Finset.prod_eq_zero (Finset.mem_univ i) (by exact norm_eq_zero.mpr hi))
     have hQ := (release_mill c x h).symm
     rw [← he,smoothBody,mul_comm] at hQ; exact mul_right_cancel₀ (by exact_mod_cast hx : ((mill x):ℂ)≠0) hQ
lemma quotient_bound {m : ℕ} (v : Test4→L[ℂ] Sum m) (h : FieldImage v) (k : @Angle m (n+1)): ∃ q : ℕ, ∃ c : chartIdx q (n+1)→ℂ, highCap c ∧
        ∀ᵐ x ∂νpow (n+1), fullWave v (n+1) x k = release c x := by
  obtain ⟨q,c,hc⟩ := shell_chart v h k
  obtain ⟨d,hd,hb⟩:= high_clean c (fun i x=>by simpa only [foot_other] using foot_vanish v h k i c hc (i.removeNth x))
  refine ⟨q,d,hb,?_⟩; rw [hd] at hc
  filter_upwards [hc,coord_dense n] with x hx hi
  exact release_on_frame k x (mill_pos hi|>.ne') d hx
end YM.Trace.Shell
