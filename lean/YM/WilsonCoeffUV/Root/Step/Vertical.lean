import YM.WilsonCoeffUV.Root.Step.Covariance
import YM.WilsonCoeffUV.Vacuum.UV.LimitGauge
/-!
# Mark vertical and gauge readout. Any finite with translation anchored.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V:Type*}{r h D l j e:ℕ} {G:Gauge}{F:Labels.Frame G h}
lemma lamp_spring (a b:G.Color)(u:Edge Cover)(j:G.ColorIndex) (k:ℕ){P:(n:Side)→ Gen ℝ (Co n (Hooks G))}{W:Gen ℝ (YForest G)}(h:∀ i,Bends 0 (fun n=>P n i) (W i))(r:ℕ)(x:Fin r→YForest G): Tendsto (fun n=> lamp a b (wrap n u.1,u.2) j k (P n) r (foldUnder n ∘ x)) atTop (𝓝 (wickLamp a b u j k W r x)):=by
  let R (n:Side):= (wrap n u.1,u.2)
  have he (y:Fin r→YForest G): Tendsto (fun n=> spore (shine (localC a b (R n) j k)) (sever (sourceEdge (R n) j) (P n)) r (foldUnder n ∘ y)) atTop (𝓝 (spore (shine (spark a b u j k)) (sever (stone u j) W) r y)):=by
    simp_rw [spore, Finset.sum_apply]; apply tendsto_finsetSum; intro i hi
    have hp:i.1+i.2=r:=Finset.mem_antidiagonal.mp hi
    by_cases hf:i.1=k; swap
    · simp_rw [shine_dark (Ne.symm hf), inter_zero_left, Pi.zero_apply]; exact tendsto_const_nhds
    let z:=y ∘ Fin.cast hp ∘ Fin.natAdd i.1
    let V: Fin (i.2+1)→ YForest G:=Fin.cons (stone u j) z
    have hV n: Fin.cons (sourceEdge (G:=G) (R n) j) (foldUnder n ∘ z)=foldUnder n ∘ V:= comps_head (stone u j) (foldUnder n)
    have hz:Tendsto (fun n=> sever (sourceEdge (G:=G) (R n) j) (P n) _ (foldUnder n ∘ z)) atTop (𝓝 (sever (stone u j) W _ z)):= by
      -- supply r+1 and exact first slot
      change Tendsto (fun n=> sever _ (P n) i.2 _) _ _
      simp_rw [sever,Pi.smul_apply,prune,hV]; have he := (h (i.2+1)).point V
      exact he.const_smul _
    subst k; simp_rw [shine_lit, interweave,dif_pos hp]; refine Tendsto.smul ?hh hz
    change Tendsto (fun n=> localC a b _ j i.1 (foldUnder n ∘ (y ∘ Fin.cast hp ∘ Fin.castAdd i.2))) _ _
    refine tendsto_const_nhds.congr' ?_
    exact (Bank.arc a b u j _ _).mono fun n hn=> hn.symm
  simp_rw [lamp,wickLamp,Blue.swirl,Pi.smul_apply,Finset.sum_apply]; exact (tendsto_finsetSum (Finset.univ (α:=Equiv.Perm (Fin r))) (fun i _=>he (x ∘ i))).const_smul ((Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹)

lemma wick_maps [AddCommGroup V][Module ℝ V] (f:V→ₗ[ℝ]ℝ)(P:Gen V (YForest G))(a b:G.Color)(u: Edge Cover)(i:G.ColorIndex)(k:ℕ): cloaks f (wickLamp a b u i k P)=wickLamp a b u i k (cloaks f P):=by
    ext1 j; rw [cloak_e]; unfold wickLamp; rw [cloak_swirl,← cloak_e, cloak_spore, cloak_sever]

structure Solo (l:ℕ)(P:Estate G D)(Q:Single G D): Prop where
   shore (i r): Bends 0 (fun n=>P n i r) (Q i r)
   launch (n:Side): shellK l (P n)
   evenS (n:Side)(i): Pure (P n i)
   oneS (n:Side) : Wreathe (P n) (P n) 1

variable {Q P} (h':Solo (G:=G) (D:=D) l P Q)
include h'
lemma solo_shape : shellK l Q:=fun i r he=> (h'.shore i r).exten (Bends.zero.congr (Eventually.of_forall fun n=> ((h'.launch n) i r he).symm))
lemma solo_pure (i): Pure (Q i):=fun r=> (h'.shore i r).pure (Eventually.of_forall fun n=> h'.evenS n i r)
lemma solo_one (t:Volume D)(n:Side): rollTest (flash (jot t (P n))) (flash (jot t (P n))) 1 0:=by
   intro Z I x X X' A; have he:= h'.oneS n t A; rw [Soil.anchor t] at he; exact he
lemma solo_bend (t:Volume D)(i r:ℕ): Bends 0 (fun n=> jot t (P n) i r) (jot t Q i r):=(h'.shore i r).touch (ContinuousLinearMap.apply ℝ ℝ t)
lemma solo_mural (r i:ℕ): mural (Q i r):= by
    intro f v x
    ext1 t; let T n:= jot t (P n); let C:=jot t Q
    let D (w:Fin r→G.ColorIndex):=fun j=>stone (v j) (w j); let b (u:Fin r→G.ColorIndex):=∏ i,gammaC f (u i) (x i)
    have he n : T n i r (slideC n (D x))=∑ u:Fin r→G.ColorIndex,b u • T n i r (slideC n (D u)):= shot_card (T n) (solo_one h' t n) (jot_length _ (h'.launch _)) (fun i=>jot_code (W:=P n) _ (h'.evenS n i)) f _ _ (fun i=>(wrap n ((v i).1), (v i).2)) x
    have hv u:Tendsto (fun n=> T n i r (slideC n (D u))) atTop (𝓝 (C i r (D u))):=(solo_bend h' t i r).point _
    simp_rw [_root_.sum_apply,_root_.smul_apply]; exact tendsto_nhds_unique (hv x) ((tendsto_finsetSum _ (fun i _=> (hv i).const_smul (b i))).congr fun n=> (he n).symm)
lemma solo_upright : vertical Q:=by
    intro b x k
    let W:= fun v:Axis=> ∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k,(wickLamp b 0 (x,v) j z.1 (Q z.2)+ wickLamp 0 b (x-step v,v) j z.1 (Q z.2)); let D':= ∑ v,W v
    ext l w t; let T n:= jot t (P n); let R:=(ContinuousLinearMap.apply ℝ ℝ t).toLinearMap
    let K(n:Side): Gen ℝ (Co n (Hooks G)) := ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (lamp b 0 (wrap n x,v) j z.1 (T n z.2)+lamp 0 b (wrap n (x-step v),v) j z.1 (T n z.2))
    have he: Tendsto (fun n=>K n l (foldUnder n ∘ w)) atTop (𝓝 (cloaks R D' l w)):=by
       unfold D' W K; simp_rw [map_sum,map_add,wick_maps,Finset.sum_apply,Pi.add_apply]; apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro j _; apply tendsto_finsetSum; intro v hv
       exact (lamp_spring b 0 (x,i) j _ (P:=fun n=> T n v.2) (solo_bend h' t v.2) _ w).add (lamp_spring 0 b (x-step i,i) j _ (P:=fun n=>T n v.2) (solo_bend h' t v.2) _ w)
    apply tendsto_nhds_unique he; refine tendsto_const_nhds.congr' ((eventually_ge_atTop (⟨2,by decide⟩: Side)).mono fun n hn=>?_)
    have hg : K n=0:=by unfold K; simp_rw [map_sub,wrap_step]; exact one_site (solo_one h' t n) _ (jot_length _ (h'.launch n)) (fun i=> jot_code (W:=P n) _ (h'.evenS n i)) hn ..
    change 0= K n l (foldUnder n ∘ w); rw [hg]; rfl
lemma solo_beam (s:G.Simple)(i): Q i 1=0:=by
    ext p t; let q:= solo_bend h' t i 1; refine tendsto_nhds_unique (q.point p) (tendsto_const_nhds.congr' (Eventually.of_forall fun n=>?_))
    change 0= jot t (P n) i 1 (slideC n p); rw [no_beam s (solo_one h' t n) (jot_length t (h'.launch n)) (fun i=> jot_code (W:=P n) _ (h'.evenS n i)) i]; rfl
lemma solo_stretch (i r): ∃ s A:ℝ,0<s∧ Twig 0 s A (Q i r):=(h'.shore i r).land
lemma solo_mercy {W X}{k}(hx:Solo k W X)(s:Signed)(p:∀ n,Wreathe (P n) (W n) s)(i r): alliance s (Q i r) (X i r):=by
    intro x c; let H n:=jot c (W n); let T n:= jot (spinV s D c) (P n)
    let Y:= fun n:Side=> H n i r (slideC n (tickW s 0 ∘ x))
    let u:=∏ j,rimSign s (x j).2
    have ha n:Y n=u*T n i r (slideC n x):=by
       unfold Y; rw [show slideC n (tickW s 0 ∘ x)= toss G s 0 ∘ slideC n x from ?_];
       · apply signed_pair (m:=k) (n:=l); intro Z K v x y ha; exact p n c ha
         exact jot_length _ (hx.launch n)
         exact jot_length _ (h'.launch n)
         exact fun i=> jot_code (W:=W n) _ (hx.evenS n i)
         exact fun i=> jot_code (W:=P n) _ (h'.evenS n i)
       ext1 j; rw [← map_zero (wrap n)];
       exact ticker s 0 (x j) n
    exact tendsto_nhds_unique (f:=Y) ((solo_bend hx c i r).point _) ((((solo_bend h' (spinV s _ c) i r).point x).const_mul u).congr (fun i=> (ha i).symm))
end YM.WilsonCoeffUV.Cosmos
