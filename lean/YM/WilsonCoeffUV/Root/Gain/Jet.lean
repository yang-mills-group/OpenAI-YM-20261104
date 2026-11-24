import YM.WilsonCoeffUV.Root.Gain.PullTest
/-!
# Sailing through the highest admitted tap grade. At leading after Ward,
transported through-slot at weight tested is **exact**. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e k a:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t A X Z D':ℝ}
-- Hull dormancy on every lower m (including empty when k=0)
def Slate (Y:ChamberTen G (Vote D) r)(F:Labels.Frame G h)(k:ℕ): Prop:= ∀ j<k,Hears F j 0 Y
lemma bare {m:ℕ}(H:Hol G)(F:Labels.Frame G h)(Y:ChamberTen G (Vote D) r)(hY:Twig 0 s A Y)(hp:0<s)(u:mural Y)(q:Smooth Y)(e:m≤h)(p:Wing 0 s 0 Y)(S:Slate Y F m) (v:Fin r→Place.Potential G)(n:Fin r→ℕ)(hv:∀ i, v i∈rangeLt _ (n i))(W:Multiset Axis)(x:(∑ i,n i)+W.card<m): pluck Y (assay ∘ v) (wallope W D)=0:=by
   obtain ⟨C,hc,h⟩:= suture F H v n W hv (k:=(∑ i,n i)+W.card) le_rfl (x.le.trans e) D hp; exact norm_le_zero_iff.mp ((h Y A 0 hY u q (S _ x) p).trans_eq (mul_zero C))
lemma total_area (n:Fin r→ℕ)(i: Fin r)(p:0<n i): (∑ j,Function.update n i (n i-1) j) < ∑ j,n j := by
   apply Finset.sum_lt_sum; · intro j _; by_cases h:j=i; · subst j; rw [Function.update_self]; omega
                              rw [Function.update_of_ne h]
   exact ⟨i,Finset.mem_univ _, by rw [Function.update_self]; omega⟩
-- generic lower-leg discard
lemma evacuate (H:Hol G)(F:Labels.Frame G h)(Y:ChamberTen G (Vote D) r)(hy:Twig 0 s A Y)(hp:0<s)(u:mural Y)(p:Smooth Y)(k:ℕ)(e:k≤h)(he:Wing 0 s 0 Y)(ht:Slate Y F k)(n:Fin r→ℕ)(hn:∀ i,0<n i)(V Q:Fin r→Place.Potential G)(hV:∀ i,V i ∈ rangeLt _ (n i))(hQ:∀ i,Q i∈ rangeLt _ (n i))(hv:∀ i,V i-Q i∈rangeLt _ (n i-1))(W:Multiset Axis)(x:(∑ i,n i)+W.card≤ k): pluck Y (assay ∘ V) (wallope W D)= pluck Y (assay ∘ Q) (wallope W D):=by
    let T (i:ℕ) (j:Fin r):= if j.val< i then V j else Q j
    have hh :∀ i≤ r, pluck Y (assay ∘ T i) (wallope W D)=pluck Y (assay ∘ Q) (wallope W D):=by
       intro i; induction i with
       | zero=> intro _; rw [show T 0=Q from funext fun _=>if_neg (Nat.not_lt_zero _)]
       | succ i ih=>
          intro hx; let v : Fin r:= ⟨i,hx⟩; let N:=Function.update n v (n v-1); let R:= Function.update (T i) v (V v-Q v)
          have hZ : assay ∘ T (i+1)= Function.update (assay ∘ T i) v (assay (V v)):=by
             funext j; by_cases h:j=v; · subst j; rw [Function.update_self,Function.comp_apply, show T (i+1) v= V v from if_pos (Nat.lt_succ_self _)]
             rw [Function.update_of_ne h]; have he:j.val≠i:=fun x=>h (Fin.ext x); simp only [Function.comp_apply,T, show j.val< i+1 ↔ j.val< i from by omega]
          have hA j:T i j∈rangeLt _ (n j):=by unfold T; split; exact hV _; exact hQ _
          rw [←ih (by omega),hZ]; apply sub_eq_zero.mp; rw [←_root_.sub_apply, pluck_grade (b:=assay ∘ T i) hy hp (fun j=>pays_assay (T i j) (hA _)) (pays_assay _ (hV v)) v]
          rw [show Function.update _ _ _=assay ∘ R from ?_]; swap
          · funext j; by_cases h:j=v; · subst j; simp only [R,Function.comp_apply,Function.update_self,show T i v=Q v from if_neg (lt_irrefl _), assay_sub]
            simp only [R, Function.comp_apply,Function.update_of_ne h]
          apply bare H F Y hy hp u p e he ht R N _ W (lt_of_lt_of_le (Nat.add_lt_add_right (total_area n v (hn _)) W.card) x); intro j; unfold R N; by_cases h:j=v; · subst j; rw [Function.update_self,Function.update_self]; exact hv _
          rw [Function.update_of_ne h,Function.update_of_ne h]; exact hA _
    specialize hh r le_rfl; rwa [show T r=V from funext fun i=>if_pos i.isLt] at hh
-- nativTop deals throughSlot guard positive.
lemma varnish (P:Patch)(w:Site P.L)(u v:Place.Potential G)(c:ℝ)(h: v∈ rangeLt _ k)(p:v-c • u∈ rangeLt _ (k-1))(e:0<k): nativ P w v-c•u∈ rangeLt _ (k-1):=by
   obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero e.ne'; rw [show nativ P w v-c • u= (nativ P w v-v)+(v-c • u) by abel]; exact Submodule.add_mem _ (Place.band_step h _) p

lemma harbour {k m:ℕ}(P:Patch)(g:Flight j k)(u0:g.L=P.L)(K:Carrier.Lines P.L)(b:ℝ)(p:0<b)(hq:HEq K (linesOf g b)) (w:Site P.L)
 (hv:4≤k)(e:h≤j)(Y:ChamberTen G (Vote D) r)(he:Twig 0 t A Y)(f:Fin r→Place.Potential G)(n:Fin r→ℕ)(hf:∀ i,f i∈ rangeLt _ (n i))(hp:∀ i,0<n i)
 (u:Wing 0 t 0 Y)(pY:Slate Y F m)(z:mural Y)(tY:Smooth Y)(h0:m≤h)(H:Hol G)(v:dragCup Bank.terrain s X (Agate P K G))(hs:0<s)(hy:s/P.L.val≤t)(W:Embroider.Spiral h)(t0:h<D)(hW:(∑ i,n i)+W.val.card ≤ m):
    pluck (pulseS P w (Agate P K G) Y) (assay ∘ f) (wallope W.val D)= (speck P)^((∑ i,n i)+W.val.card) • pluck Y (assay ∘ f) (wallope W.val D):=by
   have hu i:n i ≤ j:= (Finset.single_le_sum (f:=n) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)).trans ((Nat.le_add_right _ _).trans (hW.trans (h0.trans e)))
   have hx (L:Side)(p':L=g.L)(K:Carrier.Lines L)(x:HEq K (linesOf g b)): Whole K∧∀ i,∃ T∈rangeLt (Axis→G.Color) (n i), T-unitStep L^(n i) • f i∈rangeLt _ (n i-1) ∧ applyLine K (verdict (f i))=verdict T:=by
       subst L; have he: K=linesOf g b:= eq_of_heq x; rw [he]; exact ⟨stored g b p hv,fun i=>accepts_V b p g hv (hu i) _ (hf _)⟩
   obtain ⟨ht,hx⟩:= hx P.L u0.symm K hq
   choose o ha ho he' using hx; let T:=fun i=>nativ P w (o i)
   have hh i:T i∈rangeLt _ (n i):= Place.band_shift (ha i) _
   have ht' : 0<t:= lt_of_lt_of_le (div_pos hs (by positivity)) hy
   let Q i:= speck P^(n i) • f i; let U:=(∑ i,n i); let q:=pluck Y (fun i=>assay (T i))
   have H' : q (wallope W.val D)= speck P^U • pluck Y (assay ∘ f) (wallope W.val D):= by
       change pluck Y (assay ∘ T) _=_; rw [evacuate H F Y he ht' z tY m h0 u pY n hp T Q hh (fun i=> Submodule.smul_mem _ _ (hf i)) (fun i=>varnish P w (f i) (o i) _ (ha i) (ho i) (hp i)) W.val hW,show assay ∘ Q=fun i=> speck P^(n i) • assay (f i) from rfl, graded,_root_.smul_apply,Finset.prod_pow_eq_pow_sum]; rfl
   rw [pluck_roller P K w f n n o hf ha he' ht v hs Y he hy]; change q (foldWord P w D (page D (testa D W.val)))= _; rw [observed, Embroider.emboss P w W t0,flower_hint,map_sum,map_sum]
   let d: Embroider.Spiral W.val.card:= ⟨W.val,le_rfl⟩
   rw [Finset.sum_eq_single d]; swap
   · intro b _ hb; rw [map_smul,map_smul]; change _ • q (wallope b.val D)=0
     by_cases S:b.val.card= W.val.card; · rw [Embroider.denim b.val W.val w S (lt_of_le_of_lt W.property t0),if_neg (fun q=>hb (Subtype.ext q)),mul_zero,zero_smul]
     have ht: b.val.card<W.val.card:= lt_of_le_of_ne b.property S; rw [show q (wallope b.val D)=0 from bare H F Y he ht' z tY h0 u pY T n hh _ (lt_of_lt_of_le (Nat.add_lt_add_left ht _) hW),smul_zero]
   swap; · simp
   rw [map_smul,map_smul,Embroider.denim d.val W.val w rfl (lt_of_le_of_lt W.property t0),if_pos rfl,mul_one,pow_add]; change _ • q (wallope W.val D)=_; rw [H',smul_smul,mul_comm]
end YM.WilsonCoeffUV.Cosmos
