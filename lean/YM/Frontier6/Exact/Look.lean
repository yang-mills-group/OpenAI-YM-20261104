import YM.Frontier6.Exact.Palette

/-! Interface from annihilations up to fixed horizon to common point-detector
field projection bounds. External states not compactified away; estimates are
uniform including unselected. Constant allowed to depend on fixed exterior
word geometries and labels, not the positions in those compacts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set Lattice Wilson MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) (s:StateIndex K) {e d N:ℕ}

abbrev Reader:= StateIndex K→ (n:ℕ) → Points n → (Fin n→ S.Tag) → ℂ
variable {X:Type*}
variable (D:ℝ → Set X)(f:X→ Reader K) (σ:ℝ)
/-- admissibility `x ∈ D r` separately; arbitrary junk outside. -/
def DualEstimate : Prop:=∀ (I: Type) [_i:Fintype I] (n:I→ℕ)(v:Tuple S n)(d:ℕ)(L:Set (Seen n)), IsCompact L →
   (∀ y∈L, ∀ i:I, Points.cons 0 (y i)∈conf _)→∀ ε:ℝ,0<ε→∀ A:ℝ,0≤A→
    ∃ B:ℝ, 0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈D r, ∀ y∈L, ∀ (u:I → StateIndex K)(c:I→ℂ), (∀ i,‖c i‖ ≤ A) → kills K v y u c d →
     ‖∑ i:I, c i * f x (u i) (n i) (y i) (v i)‖ ≤ B*r^((d:ℝ)-σ-ε)

def handPoint (F:Reader K)(d:ℕ) (t:Hand K d): S.Field d:= t.recover (fun i=> F none i.val.length i.val.exterior i.val.letter)

lemma Hand.sum_read (t:Hand K d) (f:S.Field d→L[ℂ] ℂ) (v:t.list→ℂ):
   ∑ i:↥t.list, f (t.recover (Pi.single i 1)) * v i = f (t.recover v):=by
   have he (i:↥t.list):Pi.single i (v i)= v i • (Pi.single i 1: ↥t.list→ℂ):=by ext j; by_cases h:j=i <;> simp [h]
   have ht:v=∑ i:↥t.list,Pi.single i (v i):= by ext1 i; rw [Finset.sum_apply, Fintype.sum_pi_single]
   conv_rhs=>arg 2; arg 2; rw [ht]
   simp_rw [he]
   rw [map_sum,map_sum]; simp [mul_comm]
lemma form_from (y:Points N)(v:Fin N→ S.Tag)(he:e≤ d)(z:S.Field e)(h: Points.cons 0 y∈conf _): reading K s 0 y v d (higher K he z)=reading K s 0 y v e z:= form_rises K ⟨N,v,y,h⟩ s he z

lemma DualEstimate.hand_residue (h:DualEstimate K D f σ)(hL:Org.Grill C F)(t:Hand K d)(v:Fin N→ S.Tag) {L:Set (Points N)} (hK:IsCompact L)(hc:∀ y∈L,Points.cons 0 y∈conf _) (ε:ℝ)(hε:0 < ε):
   ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈ D r,∀ y∈ L, ∀ s:StateIndex K,
     ‖f x s N y v-reading K s 0 y v d (handPoint K (f x) d t)‖ ≤ B*r^((d:ℝ)+1-σ-ε):=by
   let P (y:Points N):Points (N+1):= Points.cons 0 y
   obtain ⟨b,hb,he⟩:= gap_compact (hK.image (show Continuous P by unfold P Points.cons points; fun_prop)) (image_subset_iff.mpr (show L ⊆ P ⁻¹' _ from fun x hx=> hc x hx))
   obtain ⟨C',hC,hf⟩:= reading_bounded K hL v b hb d
   let I:= Option (↥t.list)
   let n:I→ℕ
     | none=>N
     | some p=>p.val.length
   let w:Tuple S n:= fun
     | none=> v
     | some p=>p.val.letter
   let Y(y:Points N):Seen n:=fun
     | none=> y
     | some p=>p.val.exterior
   let A:= C' * ‖t.recover‖+1; have hA:1≤A:= by unfold A; linarith only [mul_nonneg hC (norm_nonneg t.recover)]
   let u(s:StateIndex K):I→ StateIndex K:=fun
     | none=>s
     | some _=> none
   let c(s:StateIndex K)(y:Points N):I→ℂ:= fun
     | none=>1
     | some p=> -(reading K s 0 y v d (t.recover (Pi.single p 1)))
   have hY: Continuous Y:= continuous_pi fun i=> by rcases i with -|p; exact continuous_id; exact continuous_const
   have hZ:∀ y∈Y '' L, ∀ i:I, Points.cons 0 (y i)∈conf _:=by rintro y ⟨x,hx,rfl⟩ (_|p); exact hc x hx; exact p.val.clear
   obtain ⟨M,hM,H⟩:= h I n w (d+1) _ (hK.image hY) hZ ε hε A (by linarith only [hA])
   refine ⟨M,hM,?_⟩
   have hv (s:StateIndex K)(y:Points N) (f:Reader K): ∑ i:I,c s y i * f (u s i) _ (Y y i) (w i) = f s N y v-reading K s 0 y v d (handPoint K f d t):=by
     rw [Fintype.sum_option]
     let F' (p:↥t.list):=f none p.val.length p.val.exterior p.val.letter
     let S':= reading K s 0 y v d
     change 1 * f s N y v + ∑ p:↥t.list, -(S' (t.recover (Pi.single p 1))) * F' p= _; rw [one_mul]; simp only [neg_mul,Finset.sum_neg_distrib,t.sum_read]; rfl -- sum_read dependent syntax
   filter_upwards [H] with r hr x hx y hy s
   rw [← hv];
   have hK': kills K w (Y y) (u s) (c s y) (d+1):=by
     intro e he z
     let F'(s:StateIndex K)(N:ℕ)(y:Points N)(v:Fin N→ S.Tag):= reading K s 0 y v e z
     have he':e ≤ d:=by omega
     have hw:handPoint K F' d t=higher K he' z:= by
       unfold handPoint; rw [show (fun p:↥t.list=>F' _ _ _ _)= _ from (?_: (fun p:↥t.list=> F' none p.val.length p.val.exterior p.val.letter)= fun p=> p.val.form K none d (higher K he' z)),t.exacts]
       ext1 p; exact (form_rises K p.val none he' z).symm
     change ∑ i:I,c s y i * F' (u s i) _ (Y y i) (w i)=0; rw [hv s y F', hw,form_from K s y v he' z (hc y hy)]; exact sub_self _
   have hA'(i:I): ‖c s y i‖ ≤ A:=by
       cases i with
       | none=> simpa [c]
       | some i=>
          change ‖-(_)‖ ≤ _; rw [norm_neg]; let C₁:= reading K s 0 y v d
          have ht:= hf s 0 y (he _ (mem_image_of_mem P hy))
          have hu:‖(Pi.single i (1:ℂ) : ↥t.list →ℂ)‖ ≤ 1:=by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; by_cases h:j=i <;> simp [h]
          apply (C₁.le_opNorm _).trans; refine le_trans (mul_le_mul ht ((t.recover.le_opNorm _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))) (norm_nonneg _) hC) ?_
          unfold A; simp
   simpa only [Nat.cast_add,Nat.cast_one] using hr x hx _ (mem_image_of_mem Y hy) (u s) (c s y) hA' hK'

lemma DualEstimate.hand_grade (h:DualEstimate K D f σ)(t:Hand K d)(w:e≤d)(ε:ℝ)(hε:0 < ε):
   ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈ D r,
     ‖weight K e (projectBelow K w (handPoint K (f x) d t))‖ ≤ B*r^((e:ℝ)-σ-ε):=by
   let I:= ↥t.list; let u:I→StateIndex K:= fun _=> none
   let n (p:I):= p.val.length; let v:Tuple S n:=fun p=>p.val.letter; let y:Seen n:=fun p=>p.val.exterior
   let a:S.Field d →L[ℂ] S.Field e:= weight K e ∘L projectBelow K w
   let g (x:X) := a (handPoint K (f x) d t)
   have he (z:S.Field e →L[ℂ] ℂ) : ∃ B:ℝ, 0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈ D r, ‖z (g x)‖≤ B*r^((e:ℝ)-σ-ε):=by
      let T:S.Field d→L[ℂ] ℂ:= z ∘L a
      let c (p:I):= T (t.recover (Pi.single p 1))
      obtain ⟨B,hB,H⟩:= h I n v e {y} (isCompact_singleton) (fun p hp i => (mem_singleton_iff.mp hp).symm ▸ i.val.clear) ε hε ‖c‖ (norm_nonneg _)
      refine ⟨B,hB,H.mono fun r hr x hx =>?_⟩
      have hk: kills K v y u c e:=by
        intro l hl q; have hw:l ≤ e:=hl.le
        have he(p:I):reading K (u p) 0 (y p) (v p) l q=p.val.form K none d (higher K w (higher K hw q)):=by rw [form_rises,form_rises]; rfl
        simp_rw [he];
        change ∑ i:I,T (t.recover (Pi.single i 1)) * _ = _; rw [t.sum_read, t.exacts]; change z (weight K e (projectBelow K w _))=_; rw [projects_fix,weight_away K q hl,map_zero]
      refine le_trans (le_of_eq ?_) (hr _ hx _ (mem_singleton y) u c (fun i=>norm_le_pi_norm c i) hk)
      exact congr_arg norm ((t.sum_read K T (fun i=> f x none i.val.length i.val.exterior i.val.letter)).symm)
   let W:=Module.finBasis ℂ (S.Field e); let J:= Fin (Module.finrank ℂ (S.Field e))
   let C' (i:J):=LinearMap.toContinuousLinearMap (W.coord i);
   choose b hb ht using fun i:J => he (C' i)
   refine ⟨∑ i:J,b i * ‖W i‖, Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (norm_nonneg _)),?_⟩
   filter_upwards [eventually_all.mpr ht] with r hr x hx
   change ‖g x‖ ≤ _; rw [← W.sum_repr (g x)]; refine (norm_sum_le ..).trans ?_; rw [Finset.sum_mul];
   exact Finset.sum_le_sum (fun i _=> by rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hr i x hx) (norm_nonneg _)).trans_eq (by ring))
end YM.Frontier6
