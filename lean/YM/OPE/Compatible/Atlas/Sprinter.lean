import YM.OPE.Compatible.Atlas.Circuits
/-!
# From screened aligned addresses to the launch. One frame at a time (uniformized on a finite menu later).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)(Q:Finset X)
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
structure Screened (C:Family G) (x:X→ E4)(m:X→ℕ):Prop where
    stops i : i∈allUp D Q →∃ y,C.S.gridPoint (m i) y = x i
    angel : angleClear D Q x ∅
variable {ψ:Filter V}{T p u: V→ℝ} {s: V→ X→ℝ} (m:V→ X→ℕ) (A:Circuit U X V)
variable (H:Tendsto T ψ atTop)(h:ClearTime D Q ψ s) {η M c δ ρ s' v f₀ L:ℝ}
set_option quotPrecheck false
local notation "P'"=> Wing D Q
variable (g:Sight)(hc:0<c)(hd:0<f₀)(hη:0<η)(hs:0<s')
   (hm: ∀ᶠ i in ψ, ∀ j∈legs D Q,m i (par D j) ≤ m i j ∧ C.S.a (m i j) /s i (par D j) ≤ 1/T i^2)
   (hP: Score ψ T p)(hp: ∀ᶠ i in ψ, ∀ x:X→ E4, Ridge (s i) (η/2) (M+1) D Q x → Screened D Q C x (m i) → u i*‖A.value i x‖ ≤ p i)
   (hv:∀ᶠ i in ψ,0 ≤ u i∧ u i ≤ Real.exp (v*T i))
include h H hm hP hη hc hd hp hs hv
lemma relaunch : ∃ w:V→ℝ,Score ψ T w∧ ∀ᶠ i in ψ,∀ x:X→E4,Ridge (s i) η M D Q x → (∀ a∈A.atoms,a.Quota D Q (s i) i x s' (Real.exp (-f₀*T i)) ∧ a.Designed i x g c) → u i * ‖A.value i x‖ ≤ w i :=by
   let n:ℝ:= (Fintype.card (Wing D Q):ℝ); let e i:=FrameRead.trail (g.code i); let L:ℝ:=1+∑ i,‖e i‖; have he(i): ‖e i‖ ≤ L:= by unfold L; exact (Finset.single_le_sum (fun i _=> norm_nonneg (e i)) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
   have hL:0<L:= add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _=>norm_nonneg _); have hn:0 ≤ n:= by unfold n; positivity
   obtain ⟨ρ,hρ,hΩ,hR⟩: ∃ ρ:ℝ,0<ρ∧ n*L*ρ ≤ min 1 (η/2) ∧ n*(L*ρ) ≤ c/2*s' :=by
       have ht : Tendsto (fun i=> n*L*i) (𝓝 (0:ℝ)) (𝓝 0):=by simpa only [id_eq,mul_zero] using! (tendsto_id (x:=𝓝 (0:ℝ))|>.const_mul (n*L))
       obtain ⟨t,h₁,h₂,h₃⟩:= ((show ∀ᶠ i in 𝓝[>] (0:ℝ), 0 < i from self_mem_nhdsWithin).and (((ht.eventually (ge_mem_nhds (show 0< min (1:ℝ) (η/2) from lt_min zero_lt_one (by positivity)))).and (ht.eventually (ge_mem_nhds (show 0 < c/2*s' by positivity)))).filter_mono nhdsWithin_le_nhds)).exists
       exact ⟨t,h₁,h₂,by rw [← mul_assoc]; exact h₃⟩
   obtain ⟨q,hq⟩:= Circuit.budgeting D Q s A H h g hc hd hs hρ he hL.le hR
   let G'(i:V)(x:X→ E4)(w:Wing D Q→ℝ) := Ridge (s i) η M D Q x ∧ (∀ a∈A.atoms,a.Quota D Q (s i) i x s' (Real.exp (-f₀*T i))∧ a.Designed i x g c)∧ ∀ j:legs D Q,x j-x (par D j)= ∑ i:Axis, w (j,i) • FrameRead.trail (g.code i)
   let Tgt (U:Finset P')(i:V)(x:X→E4)(w f:P'→ℝ):= angleClear D Q (reload D Q (s i) g x f) U ∧ (∀ j,|f j|≤ ρ) ∧ (∀ j∈U,f j=0) ∧ ∀ j, j ∉ U → Frozen D Q (s i) f (m:=m i) w (C:=C) j
   suffices hx:∀ M:Finset P', ∃ f:V→ℝ, Score ψ T f∧ ∀ᶠ i in ψ,∀ (x:X→ E4)(w y:P'→ℝ), G' i x w → Tgt M i x w y → u i* ‖A.value i (reload D Q (s i) g x y)‖ ≤ f i by
       obtain ⟨f,hκ,hY⟩:=hx Finset.univ; refine ⟨f,hκ,?_⟩; filter_upwards [hY] with i hi x he hy; obtain ⟨w,hW⟩:= coordinates D Q g x; have hz:= hi x w (fun _=>0) ⟨he,hy,hW⟩ ⟨shutter D Q _,fun j=>by simpa using hρ.le,fun _ _=>rfl,fun _ h=> (h (Finset.mem_univ _)).elim⟩; rwa [reload_base] at hz
   intro M; induction M using Finset.induction_on with
   | empty =>
       refine ⟨p,hP,?_⟩; filter_upwards [hp,hm,h.lit] with i hV hm hK x w f ⟨hi,ho,hr⟩ ⟨hy,hF,_,hf⟩; exact hV _ (perturb D h.crown x hK hF hρ.le he hL.le hi hΩ) ⟨frost D Q h.crown _ g x f w hi.belly hr (fun i hi=> (hm i hi).1) (fun j=> hf j (Finset.notMem_empty _)),hy⟩
   | insert j M hJ ih=>
       let k:=Fintype.card (X×X×Axis)+1; obtain ⟨p,hP,hπ⟩:=ih
       obtain ⟨s0,hC,hY⟩:= knurls (p:=p) H hρ k hP q v
       refine ⟨s0,hC,?_⟩; filter_upwards [hY,hv,hπ,h.lit,hm,hq] with i hi ⟨h1,h2⟩ hx hh hm hs x w f hG ⟨he,hg,hφ,hj⟩; let t:= s i (par D j.fst.1); let d:=C.S.a (m i j.fst.1); have h₃:0<t:= dim_order D h.crown hh j; have h₄:0<d:= C.S.a_pos _; obtain ⟨s₀,hM,hS⟩:= holes D Q g x f (hφ _ (Finset.mem_insert_self ..)) he h₃
       let W t':= A.value i (reload D Q (s i) g x (Function.update f j t'))
       have h:u i * ‖W 0‖ ≤ s0 i:=by
          refine hi W (u i) (hs x hG.2.1 f hg j) h1 h2 (w j/t) (d/t) (div_pos h₄ h₃) ((hm j.fst.val j.fst.2).2) s₀ (Nat.lt_succ_of_le hM) (fun t' ht hP ⟨b,hb⟩=>?_)
          refine hx x w (Function.update f j t') hG ⟨hS _ hP, fun k=>?_,fun u hu=> ?_,fun u hu=>?_⟩
          · by_cases hu:k=j; subst k; · rw [Function.update_self]; linarith only [ht,hρ]
            rw [Function.update_of_ne hu]; exact hg _
          · rw [Function.update_of_ne (by rintro rfl; contradiction : u≠j)]; exact hφ u (Finset.mem_insert_of_mem hu)
          by_cases hy:u=j
          · subst u; refine ⟨b,?_⟩; rw [Function.update_self]; change w j+t'*t= d*_; field_simp at hb; linarith only [hb]
          obtain ⟨z,hz⟩:=hj u (by simp [hy,hu]); exact ⟨z,by rw [Function.update_of_ne hy]; exact hz⟩
       have hz: Function.update f j 0=f:=by rw [← hφ j (Finset.mem_insert_self ..), Function.update_eq_self]
       unfold W at h; simpa only [hz] using h
end YM.OPE.Arboreal.Trace
