import YM.WilsonCoeffUV.Root.Step.WickTariff
/-!
# Orbital bore for fixed support & to-root thermodynamic. No dilution.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open scoped Topology BigOperators
variable {n:Side}{U α β V ι E : Type*}{k r l j:ℕ} {A B C D X Y σ η : ℝ} {d:Distance U}{w:U}{p:Cover}
variable [NormedAddCommGroup V][NormedSpace ℝ V]
variable {R:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}{P:Gen V (Cloth α)}{Q:(n:Side)→ Gen V (Co n α)}{H:Gen ℝ (Cloth α)}{K:(n:Side)→ Gen ℝ (Co n α)}
lemma Paves.rainy (h:Pilots G R)(e:Bends p (fun n=>Q n (r+2)) (P (r+2))): Paves p (fun n=> rain (G n) (Q n) r) (rain R P r):= by
  obtain ⟨u,b,hb,J⟩:= h.fees; obtain ⟨s,a,hp,H⟩:= e.price
  set w:= min u s; have hw:=lt_min hb hp
  refine ⟨fun x y=> ?_,w,_,hw,(J.and H).mono (fun n ⟨hg,hi⟩=> solorain_bill (hg.mono (min_le_left ..)) (hi.mono (min_le_right ..)) hw.le)⟩
  simp_rw [rain_spell]; have he' := e.point (Fin.cons (y 1) (Fin.cons (y 0) x));
  have hv n: Fin.cons ((slideC n y 1)) (Fin.cons (slideC n y 0) (slideC n x))=(foldUnder n ∘ Fin.cons (y 1) (Fin.cons (y 0) x)) := by rw [← comps_head,← comps_head]; rfl
  simp_rw [hv]; exact (((h.point (y 0) (y 1)).const_mul _).mul_const _ |>.mul_const _).smul he'

lemma branch_read (h:Pilots G R)(e:Yields (fun n=> K n (l+1)) (H (l+1)))(t:Bends p (fun n=> Q n (j+1)) (P (j+1)))(hv:l+j=r): Paves p (fun n=> rill (G n) (K n) (Q n) r l j) (rill R H P r l j):=by
  subst r
  have hu n:dilute (fun n=>K n (l+1)) n=K n (l+1):= if_neg (by omega)
  obtain ⟨s,a,hs,J⟩:=h.fees; obtain ⟨u,c,hc,F⟩:=e.fees; obtain ⟨v,b,hb,V⟩:=t.price
  set w:= min s (min u v); have hw:=lt_min hs (lt_min hc hb)
  refine ⟨fun x y=>?_,w,_,hw,(J.and (F.and V)).mono (fun n ⟨hg,hi,ht⟩=>by rw [hu] at hi; exact solorill_bill (hg.mono (min_le_left ..)) (hi.mono ((min_le_right ..).trans (min_le_left ..))) (ht.mono ((min_le_right ..).trans (min_le_right ..))) hw.le rfl)⟩
  simp_rw [rill_spell]; have he :=e.point (Fin.cons (y 0) (x ∘ Fin.castAdd j)); have hf:=t.point (Fin.cons (y 1) (x ∘ Fin.natAdd l)); unfold slideC at hf; simp_rw [←comps_head] at hf; simp_rw [hu,←comps_head] at he
  exact ((((h.point (y 0) (y 1)).const_mul _).mul_const _ |>.mul_const _).mul he).smul hf
lemma Paves.swiveled {F : berth α α V 2 r}{Q:canal Cover α α V 2 r}(h:Paves p F Q): Paves p (fun n=> swivel (F n)) (swivel Q):= by
    obtain ⟨s,c,ht,H⟩:=h.price; refine ⟨fun x y=>?_,s,c,ht,H.mono (fun n hn=> soloswivel_cup hn)⟩
    unfold swivel; simp_rw [Pi.smul_apply,Finset.sum_apply]; exact tendsto_const_nhds.smul (tendsto_finsetSum _ fun i _=> h.point (x ∘ i) y)

variable [Fintype α]
def rime (K:ropes Cover α α)(P:Gen V (Cloth α)) : Gen V (Cloth α):= fun r=> ruins (rain K P r)
def rondel (K:ropes Cover α α)(P:Gen ℝ (Cloth α))(Q:Gen V (Cloth α)): Gen V (Cloth α) := fun r=> ∑ j∈ Finset.antidiagonal r, ruins (swivel (rill K P Q r j.1 j.2))
variable [CompleteSpace V]
lemma rime_period (h:Pilots G R)(e:Bends p (fun n=>Q n (r+2)) (P (r+2))): Bends p (fun n=>ripple (G n) (Q n) r) (rime R P r):= by simp_rw [←rain_reads]; exact (Paves.rainy h e).rest
omit [Fintype α] [CompleteSpace V] [NormedSpace ℝ V] in
lemma leaderT {s:Finset ι}{P: (n:Side)→ ι → Gen V (Co n α)}{F:ι→ Gen V (Cloth α)}(h:∀ i∈s,Bends p (fun n=>P n i r) (F i r)): Bends p (fun n=>(∑ i∈s,P n i) r) ((∑ i∈s,F i) r):= by
    simp_rw [Finset.sum_apply]; exact (Bends.sum h).congr (Eventually.of_forall fun n=>by rw [Finset.sum_apply])
lemma rondel_period (h:Pilots G R)(e:∀ i≤r+1,Yields (fun n=> K n i) (H i))(t:∀ i≤r+1,Bends p (fun n=>Q n i) (P i)) : Bends p (fun n=>arbor (G n) (K n) (Q n) r) (rondel R H P r):=by
  have hw (i:ℕ×ℕ)(hh:i∈ Finset.antidiagonal r):=
    (branch_read h (e (i.1+1) (by have hh:=Finset.mem_antidiagonal.mp hh; omega)) (t (i.2+1) (by have hh:= Finset.mem_antidiagonal.mp hh; omega)) (Finset.mem_antidiagonal.mp hh)).swiveled.rest
  refine (Bends.sum hw).congr (Eventually.of_forall fun n=>?_); rw [Finset.sum_apply]; exact rill_reads (G n) (K n) (Q n) r
end YM.WilsonCoeffUV.Soil
