import YM.WilsonCoeffUV.Thermo.WickTariff
/-!
# Thermodynamic calculus for bulk formal vacuum (unshifted, ANY fixed components).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r l j:ℕ}
variable [NormedAddCommGroup V][NormedSpace ℝ V]

-- transports
variable {R:ropes Cover α α}{G:(n:Side)→ ropes (Site n) α α}{P:Gen V (Cloth α)}{Q:(n:Side)→ Gen V (Co n α)}{H:Gen ℝ (Cloth α)}{K:(n:Side)→ Gen ℝ (Co n α)}
lemma Tremor.rainy (h:Pilots G R)(e:Yields (fun n=>Q n (r+2)) (P (r+2))): Tremor (fun n=> rain (G n) (Q n) r) (rain R P r):= by
  obtain ⟨u,b,hb,J⟩:= h.fees; obtain ⟨s,a,hp,H⟩:= e.fees
  have he n:dilute (fun n=> Q n (r+2)) n=Q n (r+2):=if_neg (by omega)
  set w:= min u s; have hw:=lt_min hb hp
  refine ⟨fun x y=> ?_,?_,w,_,hw,(J.and H).mono (fun n ⟨hg,hi⟩=>by rw [he] at hi; exact rain_bill (hg.mono (min_le_left ..)) (hi.mono (min_le_right ..)) hw.le)⟩
  · simp_rw [rain_spell]; have he' := e.point (Fin.cons (y 1) (Fin.cons (y 0) x)); simp_rw [he] at he'
    have hv n: Fin.cons ((slideC n y 1)) (Fin.cons (slideC n y 0) (slideC n x))=(foldUnder n ∘ Fin.cons (y 1) (Fin.cons (y 0) x)) := by
      rw [← comps_head,← comps_head]; rfl
    simp_rw [hv]; exact (((h.point (y 0) (y 1)).const_mul _).mul_const _ |>.mul_const _).smul he'
  filter_upwards [h.move,e.strolls] with n hn hv
  intro b x y; simp_rw [rain_spell, Function.comp_apply, hn b _ _ , comps_head,hv b _]

lemma branch_point (h:Pilots G R)(e:Yields (fun n=> K n (l+1)) (H (l+1)))(t:Yields (fun n=> Q n (j+1)) (P (j+1)))(hv:l+j=r): Tremor (fun n=> rill (G n) (K n) (Q n) r l j) (rill R H P r l j):=by
  subst r
  have hu n:dilute (fun n=>K n (l+1)) n=K n (l+1):= if_neg (by omega)
  have hh n:dilute (fun n=>Q n (j+1)) n=Q n (j+1):=if_neg (by omega)
  obtain ⟨s,a,hs,J⟩:=h.fees; obtain ⟨u,c,hc,F⟩:=e.fees; obtain ⟨v,b,hb,V⟩:=t.fees
  set w:= min s (min u v); have hw:=lt_min hs (lt_min hc hb)
  refine ⟨fun x y=>?_,?_,w,_,hw,(J.and (F.and V)).mono (fun n ⟨hg,hi,ht⟩=>by rw [hh] at ht; rw [hu] at hi; exact rill_bill (hg.mono (min_le_left ..)) (hi.mono ((min_le_right ..).trans (min_le_left ..))) (ht.mono ((min_le_right ..).trans (min_le_right ..))) hw.le rfl)⟩
  · simp_rw [rill_spell]; have he :=e.point (Fin.cons (y 0) (x ∘ Fin.castAdd j)); have hf:=t.point (Fin.cons (y 1) (x ∘ Fin.natAdd l)); simp_rw [hh,←comps_head] at hf; simp_rw [hu,←comps_head] at he
    exact ((((h.point (y 0) (y 1)).const_mul _).mul_const _ |>.mul_const _).mul he).smul hf
  filter_upwards [h.move,e.strolls,t.strolls] with n hn hb hy
  intro b x y; simp_rw [rill_spell,Function.comp_apply, hn b _ _, Function.comp_assoc,comps_head,hb b _,hy b _]
lemma Tremor.swiveled {F : berth α α V 2 r}{Q:canal Cover α α V 2 r}(h:Tremor F Q): Tremor (fun n=> swivel (F n)) (swivel Q):= by
  let A (v:Equiv.Perm (Fin r)) (n) : canal (Site n) α α V 2 r:= fun x y=>F n (x ∘ v) y
  let B (v:Equiv.Perm (Fin r)) :canal Cover α α V 2 r:= fun x y=>Q (x ∘ v) y
  have he v:Tremor (A v) (B v):=by
    obtain ⟨s,a,hp,H⟩:=h.stood; refine ⟨fun x y=> h.point (x ∘ v) y,h.move.mono (fun n hn b x y=> hn b (x ∘ v) y),s,a,hp,H.mono fun n hn=>⟨hn.1,fun x y=>?_⟩⟩
    rw [← course_roll (tor n) x y v]; exact hn.2 ..
  unfold swivel; set K:ℝ:=(Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹; rw [show (fun n=> K • _)=K • ∑ v, A v from funext fun n=> by simp_rw [Pi.smul_apply, Finset.sum_apply]; rfl]
  exact (Tremor.sum _ (fun i _=>he i)).smul _

omit [NormedSpace ℝ V] in
lemma pair_apply [Fintype U](P:(Fin 2→U)→V): ∑ i,P i=∑ i:U,∑ j:U,P ![i,j] := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _: Fin 2=> U)), Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) U).symm]; exact Finset.sum_congr rfl fun j _=> congr_arg P (by ext k; fin_cases k <;>rfl)

variable [Fintype α]
lemma rain_reads (K:ropes (Site n) α α)(P:Gen V (Co n α))(r): wear (rain K P r)=ripple K P r := by
  funext x; rw [wear,pair_apply]; rw [ripple_form]; simp_rw [Finset.sum_apply,Pi.smul_apply]; rfl
-- no cost at rank sum reorder.
lemma rill_reads (K:ropes (Site n) α α)(P:Gen ℝ (Co n α))(Q:Gen V (Co n α))(r): (∑ j∈ Finset.antidiagonal r, wear (swivel (rill K P Q r j.1 j.2))) = arbor K P Q r:=by
  funext x
  have hp (F:canal (Site n) α α V 2 r): wear F x=∑ i: Co n α,∑ j: Co n α,F x ![i,j]:=pair_apply (F x)
  simp_rw [Finset.sum_apply,hp]
  rw [arbor_form,Finset.sum_comm]; simp_rw [Finset.sum_apply,Pi.smul_apply]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  rw [spore, swirl_sum]; simp_rw [Finset.sum_apply, Finset.smul_sum]; apply Finset.sum_congr rfl; intro p _
  simp_rw [swirl, swivel,Pi.smul_apply,Finset.sum_apply]; rw [smul_comm (K i j/2)]; simp only [Finset.smul_sum]; rfl

def crimp (K:ropes Cover α α)(P:Gen V (Cloth α)) : Gen V (Cloth α):= fun r=> worn (rain K P r)
def whittle (K:ropes Cover α α)(P:Gen ℝ (Cloth α))(Q:Gen V (Cloth α)): Gen V (Cloth α) := fun r=> ∑ j∈ Finset.antidiagonal r, worn (swivel (rill K P Q r j.1 j.2))
variable [CompleteSpace V]
lemma crimp_period (h:Pilots G R)(e:Yields (fun n=>Q n (r+2)) (P (r+2))): Yields (fun n=>ripple (G n) (Q n) r) (crimp R P r):= by simp_rw [←rain_reads]; exact (Tremor.rainy h e).transfers
omit [Fintype α] [CompleteSpace V] in
lemma parcelY {s:Finset ι}{P: (n:Side)→ ι → Gen V (Co n α)}{F:ι→ Gen V (Cloth α)}(h:∀ i∈s,Yields (fun n=>P n i r) (F i r)): Yields (fun n=>(∑ i∈s,P n i) r) ((∑ i∈s,F i) r):= by
  simp_rw [Finset.sum_apply]; exact (Yields.sum _ h).congr (Eventually.of_forall fun n=>by rw [Finset.sum_apply])
lemma whittle_period (h:Pilots G R)(e:∀ i≤r+1,Yields (fun n=> K n i) (H i))(t:∀ i≤r+1,Yields (fun n=>Q n i) (P i)) : Yields (fun n=>arbor (G n) (K n) (Q n) r) (whittle R H P r):=by
  have hw (i:ℕ×ℕ)(hh:i∈ Finset.antidiagonal r):=
    (branch_point h (e (i.1+1) (by have hh:=Finset.mem_antidiagonal.mp hh; omega)) (t (i.2+1) (by have hh:= Finset.mem_antidiagonal.mp hh; omega)) (Finset.mem_antidiagonal.mp hh)).swiveled.transfers
  exact (Yields.sum _ hw).congr (Eventually.of_forall fun n=>by rw [Finset.sum_apply]; exact rill_reads (G n) (K n) (Q n) r)

end YM.WilsonCoeffUV.Bank
