import YM.WilsonCoeffUV.FieldRead.Engineering
/-! Aggregate π/alphabet map and finite naturality. Coin/e+r_<.
Affine-null is a propagated *series equation*. Truncation at e only mixed
with lower k≥0. Hol convention h throughout.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Power
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider Fountain
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l m n p e:ℕ}{A C s t :ℝ}

abbrev Single (G:Gauge)(D):= Pal (Vote D) (YForest G)

section
variable (F:Frame G h)

def brow (i:Alma F) D:= page D (testa D (notar F i).val)
def trellis (p: ChamberTen G (Vote D) r)(i:Alma F): ℂ:= Bell F (weave F i) (valence F i) (arret (brow F i D) p h (valence F i)) (sheet F i)
def echoS (p:ChamberTen G (Vote D) r)(i: Alma F):ℝ:= (trellis F p i).re

-- Used for Strict equation kjet: start at actual e+r shift; X-adic.
def glean (p:Single G D)(e:ℕ)(i:Alma F):ℝ:= let l:=valence F i; ∑ r ∈ Finset.range (l+1), if l≤e+r then echoS F (p (e+r-l) r) i else 0

lemma trellis_real (H:Hol G){P:ChamberTen G (Vote D) r}(q: Twig 0 s A P)(hs:0<s)(v: mural P)(i:Alma F): trellis F P i=(echoS F P i:ℂ):=by
    have he:= congr_fun (bell_mood F _ _ (seed_paint H (brow F i D) q hs v h (valence F i) (show weave F i≤ h from F.bound (sheet F i)))) (sheet F i)
    refine Complex.ext rfl ?_; have ht:= congr_arg Complex.im he; change -(trellis F P i).im=(trellis F P i).im at ht; rw [Complex.ofReal_im]; linarith
lemma echo_cost (p:ChamberTen G (Vote D) r)(i:Alma F)(x:Twig 0 s A p)(he:0<s):
    ‖echoS F p i‖≤ ‖Bell F (weave F i) (valence F i)‖*(plaud G h s r (valence F i)*A*‖brow F i D‖):=
    le_trans (Complex.abs_re_le_norm _) ((norm_le_pi_norm (Bell F (weave F i) (valence F i) (arret (brow F i D) p h (valence F i))) (sheet F i)).trans (((Bell F _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_left (arret_cost _ _ _ _ x he) (norm_nonneg _))))

omit F in lemma arret_sub {P Q:ChamberTen G (Vote D) r}(c:Volume D)(h l)(v:Twig 0 s A P)(u:Twig 0 t C Q)(p:0<s)(q:0<t): arret c (P-Q) h l=arret c P h l-arret c Q h l:=by
    unfold arret; simp_rw [Pi.sub_apply,sub_apply, sub_smul]; exact ((arret_bill _ _ _ _ v p).2.1.of_norm.tsum_sub ((arret_bill _ _ _ _ u q).2.1.of_norm))
omit F in lemma arret_smul (c:Volume D)(r:ℝ)(h l:ℕ)(f:ChamberTen G (Vote D) m): arret c (r•f) h l=r • arret c f h l:=by
    unfold arret; simp_rw [Pi.smul_apply,_root_.smul_apply,smul_assoc,tsum_const_smul'']
omit F in lemma arret_grow (c:Volume D)(r:ℝ)(h l:ℕ)(f:ChamberTen G (Vote D) m): arret (r•c) f h l =r • arret c f h l:=by
    unfold arret; simp_rw [map_smul,smul_assoc, tsum_const_smul'']
omit F in lemma arret_add {P Q: ChamberTen G (Vote D) r}(c:Volume D)(h l)(v:Twig 0 s A P)(u:Twig 0 t C Q)(p:0<s)(q:0<t) : arret c (P+Q) h l= arret c P h l+arret c Q h l:=by
    unfold arret; simp_rw [Pi.add_apply, _root_.add_apply, add_smul]; exact ((arret_bill _ _ _ _ v p).2.1.of_norm.tsum_add ((arret_bill _ _ _ _ u q).2.1.of_norm))
lemma echo_minus (i:Alma F){P Q:ChamberTen G (Vote D) r}(x:Twig 0 s A P)(y:Twig 0 t C Q)(p:0<s)(q:0<t): echoS F (P-Q) i= echoS F P i- echoS F Q i:=by unfold echoS trellis; rw [arret_sub _ _ _ x y p q,map_sub]; rfl
lemma echo_mu (i:Alma F)(p:ChamberTen G (Vote D) r)(c:ℝ): echoS F (c • p) i=c • echoS F p i:=by unfold echoS trellis; rw [arret_smul,map_smul,Pi.smul_apply]; rw [Complex.smul_re]
lemma echo_zero (D r:ℕ)(i: Alma F): echoS F (0:ChamberTen G (Vote D) r) i=0:= by simp [echoS,trellis,arret]
lemma echo_dark (i:Alma F)(p:ChamberTen G (Vote D) r)(he:valence F i<r): echoS F p i=0:= by unfold echoS trellis; rw [arret_under _ _ he,map_zero]; rfl

lemma glean_mu (v:Single G D)(i:Alma F)(c:ℝ): glean F (c • v) e i=c • glean F v e i:= by
   unfold glean; dsimp only; rw [Finset.smul_sum]; simp_rw [Pi.smul_apply]; apply Finset.sum_congr rfl; intro r _; split; · exact echo_mu F i _ c
   simp
lemma tail_glint (y:Single G D)(i:Alma F)(k:ℕ): glean F y k i= (∑ r∈ Finset.range (valence F i), if valence F i≤k+r then echoS F (y (k+r-valence F i) r) i else 0)+echoS F (y k (valence F i)) i:= by simp [glean, Finset.sum_range_succ]
lemma g_lone (i:Alma F)(p:Single G D): glean F p 0 i= echoS F (p 0 (valence F i)) i:= by
    rw [tail_glint,Finset.sum_eq_zero]; · exact zero_add _
    intro r t; exact if_neg (by have := Finset.mem_range.mp t; omega)
lemma glean_sub (i:Alma F){P Q:Single G D}(v:∀ g≤e,∀ r≤valence F i,∃ s t A C,0<s∧0<t∧Twig 0 s A (P g r)∧Twig 0 t C (Q g r)): glean F (P-Q) e i=glean F P e i-glean F Q e i:=by
   unfold glean; dsimp only; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro r h; have hg:=Finset.mem_range.mp h; split <;>rename_i hx
   · obtain ⟨s,t,A,C,h,h',a,b⟩:= v (e+r-valence F i) (by omega) r (by omega); exact echo_minus F i a b h h'
   rw [sub_zero]

lemma echo_whirl (H:Hol G)(σ:Signed)(hp:h<D)(i:Alma F)(P Q:ChamberTen G (Vote D) r)(g:alliance σ P Q)(p:Twig 0 s A P)(q:Twig 0 t C Q)(hs:0<s)(ht:0<t)(hu:mural P)(hv:mural Q):
    echoS F Q i = ∑ j,blueIn F σ i j*echoS F P j:=by
   obtain ⟨u,hh,hi⟩:= drift F σ i
   let c:= page D (testa D u.val); let n:= weave F i; let l:= valence F i; let T:= Bell F n l (arret c P _ _)
   have he: spinV σ D (brow F i D)= hue σ u.val • c:=by unfold brow; rw [show notar F i=spindle σ u from congr_arg Prod.snd hi]; exact Embroider.turning _ _ hp
   have ha j (w:notar F j=u)(e:F.grades (sheet F j)=F.grades (sheet F i)): echoS F P j=(T (sheet F j)).re:= by unfold echoS trellis brow weave valence; rw [e,w]; rfl
   rw [reducing F σ (sheet F i) u n hh rfl i hi (echoS F P) (fun j=> (T j).re) ha]; unfold echoS trellis
   rw [seam F H _ _ _ (show weave F i≤ h from F.bound (sheet F i)) σ P Q g p q hs ht hu hv, pulp,he,arret_grow,map_smul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; rw [Pi.smul_apply,Complex.smul_re, smul_eq_mul]; unfold T n l; ring

lemma glean_spin (H:Hol G)(σ: Signed)(he:h<D)(i:Alma F)(P Q:Single G D)
    (a:∀ j, j≤ e → ∀ r ≤ valence F i, alliance σ (P j r) (Q j r) ∧mural (P j r) ∧ mural (Q j r) ∧ ∃ s t A C,0<s ∧ 0<t ∧ Twig 0 s A (P j r)∧ Twig 0 t C (Q j r)): glean F Q e i=∑ j, blueIn F σ i j*glean F P e j:=by
   let l:= valence F i
   let f : Alma F→ ℕ→ℝ := fun j r=> if l≤e+r then echoS F (P (e+r-l) r) j else 0
   have ht j: blueIn F σ i j*glean F P e j= ∑ r∈Finset.range (l+1),blueIn F σ i j*f j r:=by
      by_cases H : blueIn F σ i j=0; · simp [H]
      have ht: valence F j=l:= Eq.symm <| (show valence F i=valence F j from (Prod.mk.inj (mien F σ i j H).1).2)
      rw [← Finset.mul_sum]; unfold glean f; dsimp only; rw [ht]
   unfold glean
   change _=∑ j, blueIn F σ i j*glean F P e j
   simp_rw [ht]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro r h; by_cases hk:l≤e+r
   · have ht:= Finset.mem_range.mp h
     rw [if_pos hk]; simp only [f,if_pos hk]; obtain ⟨H',u,v,s,t,X,Y,hs,hs',p,q⟩:= a (e+r-l) (by unfold l; omega) r (by omega)
     exact echo_whirl F H σ he i _ _ H' p q hs hs' u v
   simp only [if_neg hk,f,mul_zero,Finset.sum_const_zero]; unfold l at hk; rw [if_neg hk]
end
end YM.WilsonCoeffUV.Cosmos
