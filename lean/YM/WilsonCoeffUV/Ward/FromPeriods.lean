import YM.WilsonCoeffUV.Thermo.Context
import YM.WilsonCoeffUV.Ward.OneSite
import YM.Gauge.Casimir
/-!
# Impulsive Ward at limit, with literal sign and gradient bookkeeping
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{n: Side}

lemma colI (h:G.Simple) : Nonempty G.ColorIndex := by
  by_contra H
  haveI : IsEmpty G.ColorIndex:= not_nonempty_iff.mp H
  haveI: Subsingleton G.Color:= ⟨fun x y=> by ext i; exact isEmptyElim i⟩
  haveI := h.nontrivial_color
  exact not_nontrivial G.Color inferInstance

def stone (x:Edge Cover)(j:G.ColorIndex) : YForest G := (x.1,coord x.2,j)
lemma wrap_stone (x:Edge Cover)(j:G.ColorIndex)(n): foldUnder n (stone x j)=sourceEdge (wrap n x.1,x.2) j:=rfl

def ringS (s:Signed)(b:Cover) (x:Edge Cover): Edge Cover:= ((posDir x.2).rotate s).used (affine s b x.1)

def rimSign (s:Signed)(i:Hooks G): ℝ:= if s.flip (axisEquiv.symm i.1) then -1 else 1

def tickW (s:Signed)(b:Cover)(w:YForest G): YForest G:= stone (ringS s b (w.1,axisEquiv.symm w.2.1)) w.2.2
lemma tick_stone (s:Signed)(b:Cover)(u:Edge Cover)(i:G.ColorIndex): tickW s b (stone u i)=stone (ringS s b u) i := by unfold tickW; simp [stone, ← coord_map]
lemma rim_stone (s:Signed)(u: Edge Cover)(i:G.ColorIndex): rimSign s (stone u i).2= if s.flip u.2 then (-1:ℝ) else 1:=by simp [rimSign,stone, ←coord_map]
lemma every_stone (x:YForest G): ∃ v j, stone v j=x := by refine ⟨(x.1,axisEquiv.symm x.2.1),x.2.2,?_⟩; simp [stone, ← coord_map]
lemma ticker (s:Signed)(b:Cover)(u:YForest G)(n: Side): foldUnder n (tickW s b u) = toss G s (wrap n b) (foldUnder n u):=by
  obtain ⟨⟨x,v⟩,j,rfl⟩:=every_stone u
  rw [tick_stone,wrap_stone,wrap_stone]; unfold sourceEdge; rw [toss_at]
  unfold ringS sendEdge; cases hx:s.flip v<;> simp [Step.rotate,posDir,hx,Step.used,affine]

-- Exact corresponding cover lamp. Direct fade in finite template. Retains even
-- higher-order Ward derivatives. Passive values module port.
section
variable (a b:G.Color)(u:Edge Cover)(j:G.ColorIndex)

def spark (k:ℕ) : Ten ℝ (YForest G) k := fade (spear (stone u)) (shine (rye (electric a b j) k)) k

def wickLamp {X:Type*}[AddCommGroup X][Module ℝ X] (k:ℕ)(P:Gen X (YForest G)): Gen X (YForest G):=fun r=>swirl (spore (shine (spark a b u j k)) (sever (stone u j) P) r)
lemma arc (k:ℕ)(x : Fin k→ YForest G) : ∀ᶠ n:Side in atTop, localC a b (wrap n u.1,u.2) j k (foldUnder n ∘ x)= spark a b u j k x:=by
  filter_upwards [eventually_all.mpr fun v=>eventually_all.mpr fun i=> fold_faith (x v) (stone u i)] with n hn
  unfold localC spark fade; apply Finset.sum_congr rfl; intro i _; congr 1; apply Finset.prod_congr rfl; intro p _
  have hh:= hn p (i p)
  simp only [spear,Matrix.of_apply,Function.comp_apply,←wrap_stone u (i p) n,hh]
lemma lamp_tend (k:ℕ){P:(n:Side)→ Gen ℝ (Co n (Hooks G))}{W:Gen ℝ (YForest G)}(h:∀ i,Yields (fun n=>P n i) (W i))(r:ℕ)(x:Fin r→YForest G): Tendsto (fun n=> lamp a b (wrap n u.1,u.2) j k (P n) r (foldUnder n ∘ x)) atTop (𝓝 (wickLamp a b u j k W r x)):=by
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
      simp only [dilute, Nat.succ_ne_zero,↓reduceIte] at he
      exact he.const_smul _
    subst k; simp_rw [shine_lit, interweave,dif_pos hp]; refine Tendsto.smul ?hh hz
    change Tendsto (fun n=> localC a b _ j i.1 (foldUnder n ∘ (y ∘ Fin.cast hp ∘ Fin.castAdd i.2))) _ _
    refine tendsto_const_nhds.congr' ?_
    exact (arc a b u j _ _).mono fun n hn=> hn.symm
  simp_rw [lamp,wickLamp,Blue.swirl,Pi.smul_apply,Finset.sum_apply]; exact (tendsto_finsetSum (Finset.univ (α:=Equiv.Perm (Fin r))) (fun i _=>he (x ∘ i))).const_smul ((Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹)
lemma spark_zero : spark a b u j 0=fun _=>(a-b) j:=by ext x; obtain ⟨n,hn⟩:=(arc a b u j 0 x).exists; rw [local_ground] at hn; exact hn.symm
lemma wick_pos {X:Type*}[AddCommGroup X][Module ℝ X](P:Gen X (YForest G)){e r:ℕ}(h:r<e): wickLamp a b u j e P r=0:=by
  unfold wickLamp; rw [show spore _ _ _=0 from ?_,swirl_exact Smooth.zero]
  apply Finset.sum_eq_zero; intro i hi; rw [shine_dark (by have hk:= Finset.mem_antidiagonal.mp hi; omega), inter_zero_left]
lemma wick_leg {X:Type*}[AddCommGroup X][Module ℝ X](P:Gen X (YForest G)){e r:ℕ}(h:e≤r): wickLamp a b u j e P r= swirl (interweave (spark a b u j e) (sever (stone u j) P (r-e)) r) := by
  unfold wickLamp spore; rw [Finset.sum_eq_single_of_mem (e,r-e)]
  · simp only [shine_lit]
  · exact Finset.mem_antidiagonal.mpr (by omega)
  intro x hx he
  rw [shine_dark ?_, inter_zero_left]; intro ht; apply he; refine Prod.ext ht.symm ?_; have he:= Finset.mem_antidiagonal.mp hx; change x.2=r-e; omega
lemma wick_beg {X:Type*}[AddCommGroup X][Module ℝ X](P:Gen X (YForest G))(h:Pure P): wickLamp a b u j 0 P=(a-b) j • sever (stone u j) P:= by
  ext1 r; rw [wick_leg _ _ _ _ _ (Nat.zero_le r)];
  have ht : interweave (spark a b u j 0) (sever (stone u j) P r) r=(a-b) j • sever (stone u j) P r:= by
    funext q; rw [spark_zero, interweave,dif_pos (by omega),Pi.smul_apply]; congr 2; funext i; change q _=q i; congr 1; apply Fin.ext; simp
  rw [Nat.sub_zero,ht]; exact swirl_exact ((pure_sever (stone u j) h _).smul _)
end
section affection
variable {P:Canvas G}
def swing (P:Pal ℝ (YForest G)): Prop:= ∀ (s:Signed)(b:Cover)(e r)(x : Fin r→YForest G), P e r (tickW s b ∘ x) = (∏ i,rimSign s (x i).2)*P e r x

def leanTwo (P:Pal ℝ (YForest G)): Prop:= ∀ v x y,∃ k:ℝ,∀ i j:G.ColorIndex, P v 2 ![stone x i,stone y j] = if i=j then k else 0

def vertical {X:Type*}[AddCommGroup X][Module ℝ X] (P:Pal X (YForest G)): Prop:= ∀ (b:G.Color)(x:Cover)(k:ℕ), ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (wickLamp b 0 (x,v) j z.1 (P z.2) + wickLamp 0 b (x-step v,v) j z.1 (P z.2))=0

lemma omni {W:Crude G}{Z:Canvas G}(s:G.Simple)(h:∀ i r,Yields (fun n=> W n i r) (Z i r))(p:∀ n, ∃ k,shellK k (W n))(t:∀ n i,Pure (W n i))(u:∀ n,Warded (flash (W n))):
    swing Z ∧ leanTwo Z ∧ (∀ i,Z i 1=0) ∧ vertical Z:= by
  haveI := colI s
  refine ⟨fun r b e j x=>?_,fun v x y=>?_,fun v=>?_,?_⟩
  · have hv := (h e j).point x
    refine tendsto_nhds_unique ((h e j).point _) ((hv.const_mul (∏ i,rimSign r (x i).2)).congr' (Eventually.of_forall fun n=> ?_))
    have hh : foldUnder n ∘ (tickW r b ∘ x)= toss G r (wrap n b) ∘ (foldUnder n ∘ x):= funext fun i=> ticker ..
    let γ:ℝ:=∏ i,rimSign r (x i).2
    have hz: W n e j (foldUnder n ∘ (tickW r b ∘ x))= γ * W n e j (foldUnder n ∘ x):= by
      rw [hh]; exact signed_pair (u n _ _) (p n).choose_spec (p n).choose_spec (t n) (t n) ..
    simp_rw [dilute]; split <;> rename_i he
    · simp only [Pi.smul_apply,hz,smul_eq_mul]; unfold γ; ring
    exact hz.symm
  · let c : G.ColorIndex:= Classical.arbitrary _
    let H (n:Side)(i l : G.ColorIndex):= W n v 2 (foldUnder n ∘ ![stone x i,stone y l])
    have ht (i j:G.ColorIndex): Tendsto (fun n=>H n i j) atTop (𝓝 (Z v 2 ![stone x i,stone y j])):= by
      have he := (h v 2).point ![stone x i,stone y j]; simpa only [dilute, show ¬ (2:ℕ)=0 from by decide,↓reduceIte] using! he
    have he (n:Side)(i j:G.ColorIndex): H n i j= if i=j then H n c c else 0:= by
      obtain ⟨K,hp⟩:=two_shade s (u n 1 0) (p n).choose_spec (t n) v (wrap n x.1,x.2) (wrap n y.1,y.2)
      have hh (i j:G.ColorIndex): foldUnder n ∘ ![stone x i,stone y j]= ![entryS G n ((wrap n x.1,x.2),i),entryS G n ((wrap n y.1,y.2),j)]:= funext fun i=> by fin_cases i<;> rfl
      simp_rw [H,hh,hp]; simp
    refine ⟨Z v 2 ![stone x c,stone y c],fun i j=>?_⟩
    split <;> rename_i hi
    · exact tendsto_nhds_unique (ht i j) ((ht c c).congr (fun n=> by rw [he n i j,if_pos hi]))
    exact tendsto_nhds_unique (ht i j) (tendsto_const_nhds.congr (fun n=> by rw [he n i j,if_neg hi]))
  · exact (h v 1).unique (Yields.zero.congr (Eventually.of_forall fun n=> (no_beam s (u n 1 0) (p n).choose_spec (t n) v).symm))
  intro b x k
  let R (n:Side): Gen ℝ (Co n (Hooks G)) := ∑ v:Axis,∑ j:G.ColorIndex,∑ z∈Finset.antidiagonal k, (lamp b 0 (wrap n x,v) j z.1 (W n z.2)+lamp 0 b (wrap n (x-step v),v) j z.1 (W n z.2))
  have he : ∀ᶠ n in atTop,R n=0:= by
    filter_upwards [eventually_ge_atTop (⟨2,by decide⟩:Side)] with n hn
    simp_rw [R, map_sub,wrap_step]; exact one_site (u n 1 0) _ (p n).choose_spec (t n) hn ..
  ext1 l; ext1 w; refine tendsto_nhds_unique (f:=fun n=> R n l (foldUnder n ∘ w)) (l:=atTop) ?_ (tendsto_const_nhds.congr' (he.mono (fun n hn=> by change 0 = R n l _; rw [hn]; rfl)))
  simp_rw [R,Finset.sum_apply,Pi.add_apply]; apply tendsto_finsetSum; intro i _; apply tendsto_finsetSum; intro j _; apply tendsto_finsetSum; intro v hv
  exact (lamp_tend b 0 (x,i) j _ (P:=fun n=>W n v.2) (h v.2) _ w).add (lamp_tend 0 b (x-step i,i) j _ (P:=fun n=>W n v.2) (h v.2) _ w)
end affection
end YM.WilsonCoeffUV.Bank
