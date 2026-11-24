import YM.OPE.Compatible.Village.Dray
/-! Full gain at any price m allowed by the budgets, with no positive lower bound on ratios
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U: Finset X}
   {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(A:Allot C)
variable {φ:Filter I}{r m:I→ℝ}{s:I→X→ℝ}{p:X→ S.Tag}
variable {η M:ℝ}{x:I→X→E4}(hx:∀ᶠ i in φ,Ridge (s i) η M D U (away (x i) (x i ⊥)))
variable (Y:Burst D U φ r s)(hη:0<η)(hM:0 ≤ M)(hO:Lanes (F:=Λ) T.sector.derivatives)(H:Services C Λ S)
variable (a:Tones T)(d:X→ℕ)
local notation "W"=>fun i=> padding D U p a.fst (s i)
local notation "W'"=>fun v b i=>padding D (Arboreal.trim U v) (paint T v p b) a.fst (s i)
set_option quotPrecheck false
local notation "b!"=> Ward.expose ∘ p
variable {v:X}(hv:v∈ rest U)
local notation "J" => fun i u => ((rat D (s i) u)^(d u+1))⁻¹
local notation "D!"=> fun i=>frontierCoefficient D T U a (s i) (x i) p
local notation "N!"=> fun i=>nests D T d U a (s i) (x i) p
variable (hp:∀ᶠ i in φ,0 ≤ m i)(hw:∀ u∈ rest U, ∀ᶠ i in φ,m i ≤ ((rat D (s i) u)^(d u+1))⁻¹) (b:ℕ)(hb:∀ u∈rest U,d u+1≤ b)
local notation "C!"=> fun i=> schedule C b (η/2) (s i)
local notation "R!"=> fun i=> aperture D C b 2 (η/2) (r i) (s i)
variable (he:∀ᶠ i in φ, whenHigh U (schedule C b (η/2) (s i))=schedule C b (η/2) (s i) v)
include A hM hO H hx hη Y hp hw
section
include hv
lemma small_span (ha:∀ᶠ i in φ,¬ aperture D C b 2 (η/2) (r i) (s i) v ≤ schedule C b (η/2) (s i) v - 1) : PaidWeight φ r (fun i=> W i*m i) (fun i=> D! i-N! i):=by
    have ht:= Y.life D
    have h1:= breather D A H.simpleGate Y hv (by positivity:0<η/2) b ha
    have hm : Score φ r m:=(Score.power (d v+1) h1 ht).pointwise (by
        filter_upwards [hw _ hv] with i hi; dsimp [rat] at hi; simpa only [← inv_pow,inv_div] using hi) hp
    have hZ : PaidWeight φ r W (fun i=> D! i-N! i):= (solid_beam T D A hO H Y hx hη hM (picked (brim D U) p) a).sub (mean D T A hx Y hη hM hO H a d p) ((pad_up D Y _ p).mono fun _ h=>h.le) ht
    apply Score.congr (hm.product hZ); filter_upwards with i; ring
include he hb
lemma high_span (hf:Maximal (· ∈ U) v) (ha:∀ᶠ i in φ,aperture D C b 2 (η/2) (r i) (s i) v ≤ schedule C b (η/2) (s i) v -1)
   (IH:∀ b'∈shades (facets T) (d v),PaidWeight φ r (fun i=> padding D (Arboreal.trim U v) (paint T v p b') a.fst (s i)*m i) (fun i=> frontierCoefficient D T (Arboreal.trim U v) a (s i) (x i) (paint T v p b')-nests D T d (Arboreal.trim U v) a (s i) (x i) (paint T v p b'))): PaidWeight φ r (fun i=> W i*m i) (fun i=> D! i-N! i):=by
    let S' b i:= shoot D T U v b (s i) (x i) p; let z b i:=frontierCoefficient D T (Arboreal.trim U v) a (s i) (x i) (paint T v p b); let h b i:=nests D T d (Arboreal.trim U v) a (s i) (x i) (paint T v p b); let R:=shades (facets T) (d v); let H₀:=fun i=> W i*m i
    have ht:= Burst.life D Y; have hv':= pad_up D Y a.fst p; have hy:∀ᶠ i in φ,0≤ H₀ i:= (hp.and hv').mono fun i hi=>mul_nonneg hi.2.le hi.1
    have hQ:=final_tour D T v p hv Y H hO A hη hM (Nat.succ_le_iff.mpr ((Nat.zero_lt_succ _).trans_le (hb _ hv))) (he.and ha) hx a (hb _ hv)
    have hw' : PaidWeight φ r H₀ (fun i=> D! i-∑ b∈ R,S' b i*z b i):= hQ.monoWeight hy (by
       filter_upwards [hw _ hv,hv'] with i hi hV; change W i*m i ≤ _; exact le_trans (mul_le_mul_of_nonneg_left hi hV.le) (ge_of_eq (levy (p:=p) (v:=v) (U:=U) (s:=s i) (d:=d v+1) (k:=a.fst) D)))
    have hh:= PaidWeight.summon R (fun b i=> S' b i*(z b i-h b i)) ht hy (fun b hb=> send D T A hx Y hη hM hO H a hv hp b (IH b hb))
    refine (hw'.add hh hy ht).alter ?_; filter_upwards with i; rw [other_bud D T (s i) (x i) d (Burst.crown D Y) a p hv hf]; change D! i - _ + _ = _-(∑ b∈ R,S' b i*h b i); simp_rw [mul_sub,Finset.sum_sub_distrib]; abel
end
lemma mayor (p:X→ S.Tag) : PaidWeight φ r (fun i=> padding D U p a.fst (s i)*m i) (fun i=>frontierCoefficient D T U a (s i) (x i) p-nests D T d U a (s i) (x i) p):=by
    revert hx Y p hw hp; -- φ dependent after
    revert φ; apply Finset.lt_wf.induction U
    intro P ih φ hx Y hp hw p
    have ht:=Burst.life D Y; by_cases HN:(rest P).Nonempty; swap
    · have he(i:I):frontierCoefficient D T P a (s i) (x i) p - nests D T d P a (s i) (x i) p=0:=by rw [nests,dif_neg HN,sub_self]
      unfold PaidWeight; simp_rw [he,norm_zero,mul_zero]; exact Score.steady _ ht
    let b:= (rest P).sup (fun u=> d u+1)
    let K i:= schedule C b (η/2) (s i); let A' (i:I) (v:X):= aperture D C b 2 (η/2) (r i) (s i) v≤ K i v-1; let S v:= {i:I| whenHigh P (K i)=K i v}; let U':= (rest P).filter fun v=>Maximal (·∈ P) v; have hq:= Y.fresh _ (by positivity:0<η/2)
    apply Score.finitely (S:=fun v i=>i∈S v) U' ht (by
       filter_upwards [series_angle D H.simpleGate A hq b] with i hi; obtain ⟨x,hX,hy,he⟩:= Bright.lit_rules hi HN; exact ⟨x, Finset.mem_filter.mpr ⟨hX,he⟩,hy⟩)
    intro v hv; obtain ⟨hv,hX⟩:= Finset.mem_filter.mp hv; let f:= φ⊓𝓟 (S v)
    apply Score.chunk (S:=fun i=> A' i v) (ht.mono_left (show f ≤ φ from inf_le_left));
    · let g:= f⊓𝓟 {i| A' i v}; have h':g ≤ φ:= inf_le_left.trans (show f ≤ φ from inf_le_left); have hh:= hx.filter_mono h'; have hE:= Burst.pinch D Y h'
      have hF:= remains P (Burst.crown D Y) ((Finset.mem_erase.mp hv).1); exact high_span D T A hh hE hη hM hO H a d hv (hp.filter_mono h') (fun v hv=> (hw v hv).filter_mono h') b (fun v hv=> Finset.le_sup (s:= rest P) (f:=fun u=> d u+1) hv) (show S v ∈ g from le_principal_iff .. |>.1 (inf_le_left.trans (show f≤𝓟 (S v) from inf_le_right))) hX (show {i | A' i v}∈g from le_principal_iff ..|>.1 inf_le_right) (fun b hb=> ih _ (lighter _ hX.1) (φ:=g) (hh.mono fun i hi=> Ridge.heals D (filter_subset ..) _ hi) (Burst.heal D hE (filter_subset ..) hF) (hp.filter_mono h') (fun v hv=> (hw v (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1,(Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).1⟩)).filter_mono h') (paint T v p b))
    let g:= f⊓𝓟 {i|¬ A' i v}; have h': g ≤ φ:=inf_le_left.trans (show f ≤ φ from inf_le_left); exact small_span D T A (hx.filter_mono h') (Burst.pinch D Y h') hη hM hO H a d hv (hp.filter_mono h') (fun v hv=> (hw v hv).filter_mono h') b (show {i|¬ A' i v} ∈ g from le_principal_iff .. |>.1 inf_le_right)
end YM.OPE.Arboreal.Trace
