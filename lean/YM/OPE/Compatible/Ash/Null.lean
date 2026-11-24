import YM.OPE.Compatible.Ash.Crest
/-! # Align low rescaled smooth bands -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}
def endband (D:List Axis)(a:Cover)(t:ℝ)(x:E4):=Pert.Band.middle D t x * Complex.exp ((corner a (t • x):ℝ)*Complex.I)
def hotband (D:List Axis)(a:Cover)(t:ℝ)(x:E4):= (disk x:ℂ)*Pert.Band.symbol D t x * Complex.exp ((corner a (t • x):ℝ)*Complex.I)
abbrev Drone (U:Gloam)(z:(i:ℕ)→ Site (U.M i)):=∀ i,z (i+1)=(U.ratio i).embed (z i)
lemma trim_end (D:List Axis)(a:Cover)(t:ℝ)(x:E4)(hh:2 ≤ ‖x‖):endband D a t x=0:=by dsimp only [endband,middle]; rw [outermost hh,disk_out (le_trans one_le_two hh)]; simp
lemma trim_hot (D:List Axis)(a:Cover)(t:ℝ)(x:E4)(hh:1 ≤ ‖x‖):hotband D a t x=0:=by simp [hotband,disk_out hh]
variable {t s c d:ℝ}{g:ℝ→E4→ℂ}
lemma vet_nop (k:ℕ){x:E4}(he:∀ u,g u x=0): vet t k g s x=0 :=by
   induction k generalizing s with
   | zero=> exact he s
   | succ k ih=> change vet t k g _ _-t^k • vet t k g (s/t) x=0; rw [ih (s:=s), ih (s:=s/t)];simp
variable {a:Cover}{z:(i:ℕ)→Site (U.M i)}{D:List Axis}
def bandread (g:ℝ→E4→ℂ)(s:ℝ) (r:ℕ)(z:(i:ℕ)→Site (U.M i))(i:ℕ):ℂ:= ∑ p:Site (U.M i),char p (z i)*vet U.q' r g (U.h i*s) (stretch (U.h i*s) p)
lemma corona_curry (i:ℕ)(hs:0<s): corona (U.h i) s D (z i+wrap _ a)= (s:ℂ)^((D.length:ℤ)-2) * bandread (endband D a) s 0 z i:=by
   let h:=U.h i; have hh:=U.h_pos i; rw [corona_expand (U.h i) _ hh hs]
   have hx: ((U.M i).val:ℂ)*((h:ℝ):ℂ)=1:=by exact_mod_cast (mul_inv_cancel₀ (ne_of_gt (val_pos _))) -- coercion n inference?
   change ((((U.M i).val:ℂ)*((h:ℝ):ℂ))⁻¹^4* _)*_= _; rw [hx, inv_one,one_pow,one_mul]
   unfold bandread; congr 1; apply Finset.sum_congr rfl; intro p hp; change char p _ * middle D (h*s) (stretch (h*s) p) = _ * endband D a (h*s) (stretch (h*s) p)
   rw [char_add,char_wrapped,endband,show (h*s) • stretch (h*s) p= moment p from stretch_fwd _ ((mul_pos hh hs).ne') _]; ring
lemma piece_curry (i:ℕ)(hs:0<s): Pert.Band.piece (U.h i) s D (z i+wrap _ a)= (s:ℂ)^((D.length:ℤ)-2)*bandread (hotband D a) s 0 z i:=by
   let h:=U.h i; have hh:=U.h_pos i; rw [piece_unwrap hh hs]
   have hx: ((U.M i).val:ℂ)*((h:ℝ):ℂ)=1:=by exact_mod_cast (mul_inv_cancel₀ (ne_of_gt (val_pos _)))
   change ((((U.M i).val:ℂ)*((h:ℝ):ℂ))⁻¹^4* _)*_= _; rw [hx, inv_one,one_pow,one_mul]
   unfold bandread; congr 1; apply Finset.sum_congr rfl; intro p hp; change char p _ * Pert.Band.symbol D (h*s) (stretch (h*s) p) * (disk (stretch (h*s) p):ℂ) = _ * hotband D a (h*s) (stretch (h*s) p)
   rw [char_add,char_wrapped,hotband, show (h*s) • stretch (h*s) p= moment p from stretch_fwd _ ((mul_pos hh hs).ne') _]; ring
lemma tide (hh:Drone U z)(r i:ℕ)(hs:0<s)(he:U.h i*s ≤ 1)(hg:∀ u x,2 ≤ ‖x‖→g u x=0) {b:ℂ} (f:ℕ→ℂ)(hf:∀ j, f j=b*bandread g s 0 z j): glide U.q' r f i= b * bandread g s r z i:=by
   let P(i):=U.ratio i
   induction r generalizing i with
   | zero=> exact hf i
   | succ r ih =>
     have hy:U.h (i+1)*s=U.h i*s/U.q':=by rw [U.h_succ]; ring
     have hv z' (hp : z'∉ Set.range (smaller (P i))):vet U.q' r g (U.h (i+1)*s) (stretch (U.h (i+1)*s) z')=0:= vet_nop _ fun u=> hg u _ (bigger_far (P i) z' hp _ hs he)
     change glide U.q' r f i - U.q'^r • glide U.q' r f (i+1)= _; rw [ih i he, ih (i+1) (by rw [hy]; exact (starMem U.qsub.le (show U.h i*s∈ Icc 0 1 from ⟨(mul_pos (U.h_pos i) hs).le,he⟩)).2)]
     unfold bandread; let G:=fun p=>char p (z (i+1))*vet U.q' r g (U.h (i+1)*s) (stretch (U.h (i+1)*s) p); change _- _•(b*∑ p,G p)= _ -- smul hint
     rw [← (show (∑ p,G (smaller (P i) p))=∑ p,G p from ?_)]
     · simp_rw [Finset.mul_sum,Finset.smul_sum]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro p hp; simp only [G,hh i]
       rw [show stretch (U.h (i+1)*s) (smaller (P i) p)= stretch (U.h i*s) p from stretch_same (P i) p s hs, show char (smaller (P i) p) ((U.ratio i).embed (z i))=char p (z i) from smaller_sig ..]; rw [hy]; change b*_- U.q'^r • (b*(char p (z i)*_))= b*(char p (z i)*(vet U.q' r g (U.h i*s) (stretch (U.h i*s) p)-U.q'^r • vet U.q' r g (U.h i*s/U.q') (stretch (U.h i*s) p)))
       rw [Complex.real_smul,Complex.real_smul]; ring
     calc (∑ p,G (smaller (P i) p))=∑ p∈ Finset.univ.image (smaller (P i)),G p := (Finset.sum_image (by intro x _ y _ hx; exact nearer (P i) hx)).symm
          _=∑ p,G p:= Finset.sum_subset (Finset.subset_univ _) (fun j _ hj=> by
                have hh:j∉Set.range (smaller (P i)):= by rintro ⟨p,rfl⟩;exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ _))
                unfold G; rw [hv j hh,mul_zero])
end YM.OPE.Balsam
