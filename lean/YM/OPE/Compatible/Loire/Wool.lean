import YM.OPE.Compatible.Loire.Noise
/-! # Double estimand for all finite hermite pol participants. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Libra PertExtension Series GaussianScore Flock Nestle Balsam
open scoped BigOperators Classical ContDiff
variable {I:Type}[LinearOrder I]{X:ℕ→Type} [∀ i,NormedAddCommGroup (X i)][∀ i, NormedSpace ℝ (X i)][∀ i,FiniteDimensional ℝ (X i)][∀ i,MeasurableSpace (X i)][∀ i,BorelSpace (X i)]
variable {μ:(i:ℕ)→Measure (X i)} [∀ i,(μ i).IsAddHaarMeasure] {L:(i:ℕ)→Law (X i)}{A:(i:ℕ)→ I→Module.Dual ℝ (X i)}{U:Gloam}{d:I→ℕ}{K:I→I→ℝ}{k:ℕ}
-- Define on base set.S locally
open StageLight
abbrev Ced (T: Finset I)(U:Gloam) (A:(i:ℕ)→ I→ Module.Dual ℝ (X i))(L:(i:ℕ)→ Law (X i))(d:I→ℕ)(K:I→I→ℝ):=∀ a∈ T,∀ b∈ T,a≠b→ GammaSite U (d a+d b) (fun i=>(L i).wick (A i a) (A i b)-K a b)

lemma GammaSite.groom_zero (U:Gloam)(m:ℕ):GammaSite U m (0:ℕ→ℝ):=by unfold GammaSite;simp only[Pi.zero_apply,mul_zero];exact cleared_zero _
abbrev bud (s:Finset I)(d:I→ℕ):ℕ:=∑ i∈s,d i
abbrev pairAv (s:Finset I)(μ:(i:ℕ)→ Measure (X i))(L:(i:ℕ)→Law (X i))(A:(i:ℕ)→I→Module.Dual ℝ (X i))(K:I→I→ℝ)(i:ℕ):= (L i).average (μ i) (fauna K (A i) s)
lemma grime (t:Finset I)(hp:Ced t U A L d K):∃ c,Bloom U (bud t d) (pairAv t μ L A K) c:=by
   apply fromCore
   induction t using Finset.strongInduction with | _ s ih
   obtain rfl|he:=s.eq_empty_or_nonempty
   · simp [fauna,bud,pairAv,Law.empty]; exact Cleared.always
   let a:=s.min' he; let T:=s.erase a; have hh:=innerA he; have ht:T⊂s:=Finset.erase_ssubset hh.1
   let f(j:I)(i:ℕ):= (L i).wick (A i a) (A i j)-K a j
   have hv(j)(hJ:j∈T): GammaSite U (bud s d) (fun i=> f j i * pairAv (T.erase j) μ L A K i) :=by -- alias
      let R:=T.erase j
      have hx: R ⊂ s:=Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) ht
      have hf:= Finset.ssubset_iff_subset_ne.mp hx; have h':T ⊆ s:= (Finset.ssubset_iff_subset_ne.mp ht).1
      obtain ⟨B,hB⟩:= fromCore (ih R hx (fun b h x h₁ he=> hp _ (hf.1 h) _ (hf.1 h₁) he)); obtain ⟨C,hC⟩:= fromCore (hp a hh.1 j (h' hJ) (Finset.ne_of_mem_erase hJ).symm)
      rw [show bud s d=(d a+d j)+bud R d from by unfold bud; rw [← Finset.add_sum_erase _ _ hh.1]; change d a+∑ j∈T,d j=_; rw [← Finset.add_sum_erase _ _ hJ,add_assoc]]; exact (hC.pen hB).2.1
   unfold pairAv; rw [show (fun i:ℕ=>_) =(∑ j∈T, fun i=>(U.h i^(bud s d))⁻¹*(f j i*pairAv (T.erase j) μ L A K i)) from ?_]; exact Cleared.tally _ _ hv
   funext i; rw [bloom_raw (μ i) (L i) K _ hh,Finset.mul_sum,Finset.sum_apply]
abbrev Hear (μ:(i:ℕ)→ Measure (X i))(L:(i:ℕ)→ Law (X i))(A:(i:ℕ)→I→Module.Dual ℝ (X i))(K:I→I→ℝ)(f:(i:ℕ)→X i→ℝ)(s:Finset I)(i:ℕ):=(L i).average (μ i) (fauna K (A i) s*f i)
def Quill (μ:(i:ℕ)→Measure (X i))(L:(i:ℕ)→ Law (X i))(A:(i:ℕ)→I→Module.Dual ℝ (X i))(K:I→I→ℝ)(U:Gloam)(t:Finset I)(d:I→ℕ)(f:(i:ℕ)→X i→ℝ)(k:ℕ):Prop:=∀ s⊆t,Fruit U (k+bud s d) (Hear μ L A K f s) 0
abbrev twist (L:(i:ℕ)→ Law (X i))(Q:(i:ℕ)→ Module.Dual ℝ (X i))(f:(i:ℕ)→X i→ℝ)(i): X i→ℝ:= poke ((L i).inverse (Q i)) (f i)
lemma quill (f:(i:ℕ)→ X i→ℝ)(T:Finset I)(hp:Ced T U A L d K)(hf:∀ i,Bond (f i))(hb:∀ i,(L i).average (μ i) (f i)=0)(hh:∀ a∈ T, Quill μ L A K U T d (twist L (fun i=> A i a) f) (k+d a)):Quill μ L A K U T d f k:=by
   intro s hs; induction s using Finset.strongInduction with | _ s ih
   obtain rfl|he:=s.eq_empty_or_nonempty
   · rw [show Hear μ L A K f ∅=0 from funext fun i=>by unfold Hear; rw [fanE,one_mul,hb];rfl]; exact Cleared.sap (cleared_zero U)
   let a:=s.min' he; let t:=s.erase a; have ht:t ⊂ s:= Finset.erase_ssubset (innerA he).1; let C:=Hear μ L A K f; have hT:= (Finset.ssubset_iff_subset_ne.mp ht).1
   let Z:= Hear μ L A K (twist L (fun i=>A i a) f) t
   let g(j:I)(i:ℕ):= (L i).wick (A i a) (A i j)-K a j; let G(j:I)(i:ℕ):=g j i * C (t.erase j) i
   have h: ∀ j∈t, Fruit U (k+bud s d) (G j) 0:=by
      intro j hJ; let r:=t.erase j; have he: r ⊂ s:=Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) ht; have H':r⊆T:= Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp he).1 hs
      obtain ⟨x,hx⟩:=fromCore (hp a (hs (Finset.min'_mem ..)) j (hs (hT hJ)) (Finset.ne_of_mem_erase hJ).symm); rw [show G j=C r*g j from funext fun i=> mul_comm .., show 0= (0:ℝ)*x from (zero_mul _).symm, show k+bud s d=(k+bud r d)+(d a+d j) from by unfold bud; rw [← Finset.sum_erase_add _ _ (show a∈s from (Finset.min'_mem ..))]; erw [← Finset.sum_erase_add t _ hJ]; unfold r; ac_rfl]; exact (ih _ he H').pen hx
   have hl:Fruit U (k+bud s d) Z 0:=by rw [show k+bud s d=k+d a+bud t d from by unfold t bud; conv_lhs=>rw [← Finset.add_sum_erase s _ (Finset.min'_mem s he),←add_assoc]]; exact hh a (hs (Finset.min'_mem ..)) t (Finset.Subset.trans hT hs)
   rw [show Hear μ L A K f s=Z+∑ j∈t,G j from funext fun i=>by rw [Pi.add_apply,Finset.sum_apply]; exact hick (μ i) (L i) K (A i) (hf i) (innerA he),← add_zero (0:ℝ)]; refine Fruit.sum hl ?_; simpa only [Finset.sum_const_zero] using (Fruit.line t G _ h)
lemma gavel (g:ℕ→ℝ)(T:Finset I)(hp:Ced T U A L d K)(hx:Fruit U k g 0): Quill μ L A K U T d (fun i _=>g i) k:=by
   intro s hs; obtain ⟨c,h⟩:=grime (d:=d) (L:=L) (A:=A) (K:=K) (μ:=μ) s (fun i hI j hJ he=>hp _ (hs hI) _ (hs hJ) he)
   rw [show 0=(0:ℝ)*c from (zero_mul _).symm, show Hear μ L A K (fun i _=>g i) s=g*pairAv s μ L A K from funext fun i=>?_]; exact hx.pen h
   unfold Hear; rw [show fauna K (A i) s* (fun _=>g i) = (g i) • fauna K (A i) s from funext fun x=>mul_comm ..,scooted ..];rfl
end YM.OPE.Shrew
