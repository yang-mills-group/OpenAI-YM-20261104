import YM.OPE.Compatible.Estuary.June
/-!
# Mixed differential extraction. Lower terms only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I:Type}[Fintype I]{J:Type}{r n m d h:ℕ}{G:Gauge} {X:Side}
namespace Script
open Page Virgin OrderedFinpartition
lemma trounce (A: Finset (Cover × I))(F:I→ shelf A→ ℝ)(hX:∀ i, ContDiffAt ℝ ω (F i) 0)(hf:∀ i,F i 0=0)(m n:ℕ)(hn:0<n) :∃ K:ℝ,0≤ K∧∀ (q:(r:ℕ)→Script I r)(B:ℝ), 0≤B → (∀ r,0<r → r<n→ soot m (q r) B)→ ∃ p: Script I n,soot m p (K*B)∧ ∀ (l:Side)(Y: deck I l→ℝ),ContDiffAt ℝ ω Y 0→ (∀ r,0<r→ r<n→∀ i:Fin r→deck I l, iteratedFDeriv ℝ r Y 0 i=library l (q r) i)→ ∀ i:deck I l,
     iteratedFDeriv ℝ n (Y ∘ vitalX A F) 0 (fun _ => i)=iteratedFDeriv ℝ n Y 0 (fun _ =>fderiv ℝ (vitalX A F) 0 i)+narrate l p i:=by
       let v n:=ledgeB A F n; let Θ := OrderedFinpartition n
       choose K hK using fun i:Θ=> apprentices i.partSize m 0 (fun j=> v (i.partSize j)) (fun j=> ledgeBudget A F _ m)
       let L:Finset Θ := univ.erase (atomic n); let M:=max 0 (∑ i∈L,K i); refine ⟨M, le_max_left ..,fun q B hB hp=>?_⟩
       have he(i:Θ)(hx:i∈L): i.length < n:=lt_of_le_of_ne i.length_le fun hh=> (mem_erase.mp hx).1 (allSingle _ hh)
       let W(i:Θ)(l:Side)(x:deck I l):= library l (q i.length) fun j=> boom (ledgeB A F (i.partSize j)) fun _=>x
       have hz(i:Θ)(hw:i∈L) :∃ p:Script I n,soot m p (K i*B)∧∀ (l:Side)(j:deck I l), W i l j=narrate l p j:=by
           obtain ⟨p,H,hp'⟩:= hK i (q i.length) B (hp i.length (i.length_pos hn) (he i hw)); have hh: (∑ j,i.partSize j)+0=n:=by
              simpa using Fintype.card_congr i.equivSigma
           refine ⟨redact p hh,redactP _ _ H,fun l j=>?_⟩; unfold narrate; rw [redactTut]; change W i l j=narrate l p j; rw [hp', Fin.append_right_nil _ _ rfl];rfl
       choose p hb g using hz
       let P(i:Θ):= if h:i∈L then p i h else (0:Script I n); have hy(i:Θ)(h:i∈L):soot m (P i) (K i *B):=by unfold P; rw [dif_pos h]; exact hb i h
       refine ⟨∑ i∈L,P i, (Sack.finGather _ _ _ hy (fun i=> zero_le_one.trans (payer m _))).tips ?_,?_⟩
       · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) hB
       intro l Y hY hy' x; let T:=vitalX (n:=l) A F; have hh : T 0=0 := by ext1 i; unfold T vitalX; rw [map_zero,hf];rfl
       let S(i:Θ):= iteratedFDeriv ℝ i.length Y 0 fun (j:Fin i.length)=>iteratedFDeriv ℝ (i.partSize j) T 0 fun _=>x
       change iteratedFDeriv ℝ n (Y∘T) 0 _= _; rw [iteratedFDeriv_comp (show ContDiffAt ℝ ω Y (T 0) from hh.symm ▸ hY) (ledgeDiff A F hX l) le_top, hh]; unfold FormalMultilinearSeries.taylorComp; rw [_root_.sum_apply, ← Finset.add_sum_erase _ _ (mem_univ (atomic n))]; apply congr_arg₂
       · change S (atomic n)=_; unfold S; change iteratedFDeriv ℝ n Y 0 (fun j=> iteratedFDeriv ℝ 1 T 0 (fun _=> x))= _; simp only [iteratedFDeriv_one_apply]; rfl
       symm; change library l _ _=∑ i∈L,S i; unfold library; simp_rw [reads_sum L P (fun i h=> sootS (hy i h))]; rw [Finset.sum_comm]; refine sum_congr rfl fun i hi=> ?_; unfold S; rw [hy' _ (i.length_pos hn) (he i hi)]; simp_rw [show ∀ j: Fin i.length,iteratedFDeriv ℝ (i.partSize j) T 0 (fun _=>x)=_ from fun j=> ledgeFilm A F hX (r:=i.partSize j) (n:=l) (fun _=>x)]; unfold P; simp only [dif_pos hi]; exact (g i hi l x).symm
end Script
end YM.OPE.Flume
