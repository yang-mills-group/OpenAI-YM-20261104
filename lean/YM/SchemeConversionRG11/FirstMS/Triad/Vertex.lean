import YM.SchemeConversionRG11.FirstMS.Triad.Halo

/-! Integrated cubic V1 power: define from stems for each allowed incidence graph,
 MS-local-position prescription (not assuming kernel reduction). f germs may contain junk at 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

variable {x:Nodes} {R ρ:ℝ}
variable (h:Box x R ρ)(l:P→Stem)(j:P)(a:Axis)

def subgraph (k:P) (R:ℝ)(T:sheet):ℂ→ℂ:= if k=j then fun z=> -charge R (rotate (l k).dual (l k).i (l k).axis) (ridge a T) z
     else charge R (rotate (l k).dual (l k).i (l k).axis) T

def packing (x:Nodes)(R:ℝ)(i:P)(z:ℂ):ℂ:=
    let K:=cluster l i
    let T:=locals l j a x R i
    if K=∅ then vert z *billAt z (fun y=> T (z,swell y))
    else if K.card ≤ 1 then ∑ k∈K, subgraph l j a k R T z
    else pair (fun z x u=>∏ k∈K,kind l j a k z x u) T R (decide (j∈K)) z

def multiplies (x:Nodes)(R ρ:ℝ) (z:ℂ):= pivot l j a x R ρ z+high l j a x ρ z+∑ i:P,packing l j a x R i z

-- Valid domain no more than two attachments to the same mark in the connected diagram
-- (the two already by color discarded for anti-pair). P=3, one V. -3/line etc.
omit h
lemma scaled_pair (i:P) (hp:(cluster l i).card=2) :
   let K:=cluster l i; let n:= thickness (decide (j∈K))
   owns (fun z x u=>∏ k∈K,kind l j a k z x u) (fun z=>age n z - 4 - 2*z) := by
   intro K n; change K.card=2 at hp
   obtain ⟨b,c,hc,he⟩:= Finset.card_eq_two.mp hp
   intro s hs p hh t ht; dsimp only; unfold n; rw [he]; simp_rw [Finset.prod_pair hc,owns_kind l j a _ _ hs _ hh _ ht]
   have hu : (t:ℂ)≠0:= ofReal_ne_zero.mpr ht.ne'
   rw [mul_mul_mul_comm, ← cpow_add _ _ hu]
   congr 2
   by_cases hb:b=j
   · have hx:c≠j:= fun h=> hc (hb.trans h.symm)
     subst j; simp [thickness,S,hx, Ne.symm hx,age]; ring
   by_cases hm:c=j
   · subst j; simp [thickness,S,hb,Ne.symm hb,age]; ring
   simp [thickness,S,hb,hm,Ne.symm hb,Ne.symm hm,age]; ring

lemma subgraph_open {T:sheet} (hh:Touch R T) (k:P): AnalyticAt ℂ (subgraph l j a k R T) 0:= by rw [subgraph]; split_ifs; exact (funds _ _ _ (hh.gradient _) occurs).neg; exact funds _ _ _ hh occurs

/-- Projection defined only on honest completed analytic germs. -/
structure aim (F:ℂ→ℂ)(v:ℂ):Prop where
    arc : ∃ g:ℂ→ℂ, AnalyticAt ℂ g 0 ∧ F =ᶠ[walks] g ∧ g 0=v
lemma atMark {F:ℂ→ℂ}(h:AnalyticAt ℂ F 0): aim F (F 0):= ⟨F,h,EventuallyEq.rfl,rfl⟩ -- parse

lemma aim.pair_goal {F H:ℂ→ℂ}{v u} (h:aim F v)(k:aim H u):aim (fun z=> F z+H z) (v+u):= by
   obtain ⟨g,hg,he,rfl⟩:=h.arc; obtain ⟨f,hf,hh,rfl⟩:=k.arc
   exact ⟨g+f,hg.add hf,he.add hh,rfl⟩
lemma aim.prod_goal {F H:ℂ→ℂ}{v u} (h:aim F v)(k:aim H u):aim (fun z=> F z*H z) (v*u):= by
   obtain ⟨g,hg,he,rfl⟩:=h.arc; obtain ⟨f,hf,hh,rfl⟩:=k.arc
   exact ⟨g*f,hg.mul hf,he.mul hh,rfl⟩
lemma aim.bag {I:Type*}(s:Finset I){F:I→ℂ→ℂ}{v:I→ℂ}(h:∀ i∈s,aim (F i) (v i)): aim (fun z=> ∑ i∈s,F i z) (∑ i∈s,v i):= by
   induction s using Finset.induction_on with
   | empty=> simpa only [Finset.sum_empty] using (atMark (analyticAt_const (v:=(0:ℂ))))
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self ..)).pair_goal (ih fun i hi=> h _ (Finset.mem_insert_of_mem hi))
lemma aim.unique {F:ℂ→ℂ}{v u}(h:aim F v)(hh:aim F u) : v=u:= by
   obtain ⟨g,hg,he,rfl⟩:=h.arc; obtain ⟨f,hf,hH,rfl⟩:=hh.arc
   exact tendsto_nhds_unique_of_eventuallyEq (hg.continuousAt.tendsto.mono_left (show walks ≤ _ from nhdsWithin_le_nhds)) (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (he.symm.trans hH)
include h

lemma packing_pays (i:P) (hp:(cluster l i).card≤2): ∃ v, aim (packing l j a x R i) v:= by
   let T:=locals l j a x R i; have ht:Touch R T:=cut_local h l j a i
   unfold packing; dsimp only; let K:= cluster l i; change K.card≤2 at hp
   change ∃ v, aim (fun z:ℂ=> if K=∅ then vert z*billAt z (fun v=> T (z,swell v)) else if K.card≤1 then ∑ k∈K,subgraph l j a k R T z else pair (fun z x u=>∏ k∈K,kind l j a k z x u) T R (decide (j∈K)) z) v
   by_cases he: K=∅
   · simp_rw [if_pos he]; exact ⟨_,atMark ((vert_analytic.analyticAt _).fun_mul (g:=fun z=>billAt z (fun v => T (z,swell v))) ((ht.folded.integral opened).analytic opened occurs 0))⟩
   simp_rw [if_neg he]; by_cases hk:K.card≤1
   · simp_rw [if_pos hk]; exact ⟨_, aim.bag K fun i _=> atMark (subgraph_open l j a ht i)⟩
   simp_rw [if_neg hk]
   have H(K:Finset P): Off (fun z x u=>∏ k∈K,kind l j a k z x u) := by
      refine ⟨fun s hs p hp=> contDiffAt_prod fun k _=>(off_kind l j a k).smooth s hs p hp,fun s hs p hp=> DifferentiableAt.fun_finsetProd fun k _=>(off_kind l j a k).colors s hs p hp⟩
   have HX : K.card=2:= by omega
   have hw:= scaled_pair l j a i HX -- lint
   obtain ⟨g,hg,hH⟩:= pair_fin (H _) ht (decide (j∈K))
   exact ⟨g 0,g,hg,hH,rfl⟩

lemma projection (hv:∀ i,(cluster l i).card≤2): ∃ v, aim (multiplies l j a x R ρ) v := by
   choose d hd using fun i=> packing_pays h l j a i (hv i)
   exact ⟨_, ((atMark (pivot_ok h l j a)).pair_goal (atMark (high_analytic h l j a occurs))).pair_goal (aim.bag _ fun i _=> hd i)⟩

-- on canonical order of distinct stems
omit h
variable (hl:∀ i,(l i).loc=i)
include hl
lemma cluster_one (i:P): cluster l i={i} := by simp [cluster,hl]; ext; simp
lemma freezes (i:P): packing l j a x R i=subgraph l j a i R (locals l j a x R i):= by
   unfold packing; funext z; rw [cluster_one l hl]; simp
include h
lemma distinct_zero : aim (multiplies l j a x R ρ) (multiplies l j a x R ρ 0):= by
   refine ((atMark (pivot_ok h l j a)).pair_goal (atMark (high_analytic h l j a occurs))).pair_goal (aim.bag _ (fun i _=> atMark ?_))
   rw [freezes l j a hl]; exact subgraph_open l j a (cut_local h l j a _) i
end YM.SchemeConversionRG11.FirstMS.Triad
