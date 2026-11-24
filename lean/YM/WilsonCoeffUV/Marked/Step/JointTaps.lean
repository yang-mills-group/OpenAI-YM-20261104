import YM.WilsonCoeffUV.Marked.Step.LogStep
/-!
# One rooted mark joining another (Bends in Pen)

Inequality will use costs from both rooted log supports at their own origins.
This representation internal arity two links. Implements exactly sewsV.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{ι U L α:Type}{J K I S T:Finset ι}{D k:ι→ℕ}{i j e r h N m l:ℕ}{G:Gauge}{V:Type}
variable [DecidableEq ι]
omit [DecidableEq ι] in
lemma bendKin (f:U≃L)(P:Gen (Pen D S) U)(A:Case D) : cloaks (touch A S).toLinearMap (bend f P)=bend f (cloaks (touch A S).toLinearMap P):=rfl
lemma bendSean [Fintype U][Fintype L](f:U≃L)(V:Matrix U U ℝ)(b:J⊆S)(P:Layers (Pen D J) U)(Q:Layers (Pen D (S\J)) U)(i j) : bend f (sewsV V b P Q i j)=sewsV (allotM f f V) b (fun i j=> bend f (P i j)) (fun i j=>bend f (Q i j)) i j:=by
   funext r x; apply pen_inj; intro A
   let C:= (touch A S).toLinearMap; let X i j:=bend f (P i j); let Y i j:=bend f (Q i j)
   change cloaks C (bend f (sewsV V b P Q i j)) r x=cloaks C (sewsV (allotM f f V) b X Y i j) r x; rw [bendKin,sewsMap,sewsMap, bend_ravel]; rfl

-- derive BiCanal
abbrev sealM (i j:ℕ):ℝ:= (1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ)
def lakeL (V:ropes U α α)(b:J⊆ S)(P:Gen (Pen D J) (U×α))(Q:Gen (Pen D (S\J)) (U×α))(r i j:ℕ) : canal U α α (Pen D S) 2 r:=fun x y=> (V (y 0) (y 1)/2) • cobT b (sever (y 0) P i) (sever (y 1) Q j) r x
lemma lakeV (V:ropes U α α)(b:J⊆ S)(P:Gen (Pen D J) (U×α))(Q:Gen (Pen D (S\J)) (U×α))(i j:ℕ)(x y) : lakeL V b P Q (i+j) i j x y= (sealM i j* V (y 0) (y 1)) • joinL b D (P _ (Fin.cons (y 0) (x ∘Fin.castAdd j))) (Q _ (Fin.cons (y 1) (x ∘ Fin.natAdd i))):=by
   rw [lakeL,cobT,dif_pos rfl]; unfold sever; change _ • joinL b D ((i+1) • (P _ _)) ((j+1) • (Q _ _)) = _; simp_rw [← Nat.cast_smul_eq_nsmul ℝ, map_smul, _root_.smul_apply,smul_smul]; unfold sealM; congr 1; ring

lemma lakeLeaf (V:ropes U α α)(b:J⊆ S)(P:Gen (Pen D J) (U×α))(Q:Gen (Pen D (S\J)) (U×α))(A:Case D)(x y) : touch A S (lakeL V b P Q (i+j) i j x y) = rill V (cloaks (touch A J).toLinearMap P) (cloaks (touch A (S\J)).toLinearMap Q) (i+j) i j x y:=by
    rw [lakeV,map_smul,waveJoy,joy_p,rill_spell]; let v : Fin (i+1) → U×α :=Fin.cons (y 0) (x ∘ Fin.castAdd j); let t : Fin (j+1)→ U×α :=Fin.cons (y 1) (x ∘ Fin.natAdd i);
    change _ • ((touch A J (P (i+1) v):ℝ)*_)=(_ * touch A J (P _ v)) • (touch A (S\J) (Q _ t)); unfold sealM; ring
lemma lakeReads [Fintype α](V:ropes (Site n) α α)(b:J⊆S)(P:Gen (Pen D J) (Site n × α))(Q:Gen (Pen D (S\J)) (Site n × α))(r:ℕ):
     (∑ j∈Finset.antidiagonal r,refuge (swivel (lakeL V b P Q r j.1 j.2)))=logos V b P Q r:=by
    funext x; apply pen_inj; intro A
    let X:=cloaks (touch A J).toLinearMap P; let Y:=cloaks (touch A (S\J)).toLinearMap Q
    rw [show touch A S (logos _ _ _ _ _ x) =(arbor V X Y r) x from congr_fun (congr_fun (logosT A V b P Q) _) _, ← rill_reads, Finset.sum_apply, Finset.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro i hi; have hv:i.1+i.2=r:= Finset.mem_antidiagonal.mp hi
    subst r; unfold refuge wear swivel; simp only [Pi.smul_apply,Finset.sum_apply,map_sum, map_smul,lakeLeaf]; rfl

-- estimate at fixed finite roots (for thermo, n large)
lemma lakeXB {w o:U}{s a t c:ℝ}{d:Bank.Distance U}(V:ropes U α α)(b:J⊆ S)(P:Gen (Pen D J) (U×α))(Q:Gen (Pen D (S\J)) (U×α)) (p:Cork d o s a (P (i+1)))(q:Cork d w s t (Q (j+1)))(h:dragCup d s c V)(e:0≤ s): Peb d w s (sealM i j*c*a*t) (lakeL V b P Q (i+j) i j):=by
   have hc:=h.1; have ha:=p.1; have ht:=q.1; have hv:0≤ sealM i j:=by unfold sealM; positivity
   refine ⟨by positivity,fun x y=>?_⟩; let v : Fin (i+1) → U×α :=Fin.cons (y 0) (x ∘Fin.castAdd j); let f : Fin (j+1)→ U×α := Fin.cons (y 1) (x ∘ Fin.natAdd i); let X:=brims d w x y; let H:=d.gap (y 0).1 (y 1).1
   have ht:tread d o v + H + tread d w f≥ X:= (right_cup x y).trans (by exact Nat.add_le_add_right (Nat.add_le_add_right (league_le d _ fun i j=>leg_le d (stud o v) i.succ j.succ) _) _)
   rw [lakeV,norm_smul,norm_mul,Real.norm_of_nonneg hv,waveJoy]; calc
   _≤(sealM i j*(c*Real.exp (-s*H)))*((a*Real.exp (-s*tread d o v))*(t*Real.exp (-s*tread d w f))):=mul_le_mul (mul_le_mul_of_nonneg_left (h.2 ..) hv) ((joy_norm ..).trans (mul_le_mul (p.2 _) (q.2 _) (norm_nonneg _) (by positivity))) (norm_nonneg _) (by positivity)
   _=sealM i j*c*a*t*Real.exp (-s*(tread d o v + H+tread d w f : ℕ)):=by push_cast; rw [mul_add,mul_add,Real.exp_add,Real.exp_add]; ring
   _≤_:=mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr ht) (neg_nonpos.mpr e))) (by positivity)

lemma dawnB {V:(n:Side)→ ropes (Site n) α α}{K:ropes Cover α α}(b:J⊆ S){P:(n:Side)→ Gen (Pen D J) (Site n×α)}{Q:(n:Side)→ Gen (Pen D (S\J)) (Site n×α)}{X:Gen (Pen D J) (Cloth α)}{Y:Gen (Pen D (S\J)) (Cloth α)}(t:Pilots V K)(p:Bends 0 (fun n=> P n (i+1)) (X (i+1)))(q:Bends 0 (fun n=>Q n (j+1)) (Y (j+1)))(v:i+j=r):
      Paves 0 (fun n=> lakeL (V n) b (P n) (Q n) r i j) (lakeL K b X Y r i j):=by
    subst r; obtain ⟨s,a,hS,Z⟩:= t.fees; obtain ⟨x,A,hx,H⟩:=p.price; obtain ⟨y,B,hy,H'⟩:=q.price; let W:=min s (min x y); have he:= lt_min hS (lt_min hx hy)
    refine ⟨fun x y=>?_,W,_,he,(Z.and (H.and H')).mono fun n hn=> lakeXB (V n) b (P n) (Q n) (hn.2.1.mono ((min_le_right ..).trans (min_le_left ..))) (hn.2.2.mono ((min_le_right ..).trans (min_le_right ..))) (hn.1.mono (min_le_left ..)) he.le⟩
    have hp:= p.point (Fin.cons (y 0) (x ∘Fin.castAdd j)); have hq:=q.point (Fin.cons (y 1) (x ∘Fin.natAdd i)); simp_rw [lakeV]
    unfold slideC at *; simp_rw [← comps_head] at hp hq; let f (p:Pen D J× Pen D (S\J)):= joinL b D p.1 p.2; have hf:Continuous f:= ((joinL b D).continuous.comp continuous_fst).clm_apply continuous_snd
    exact ((t.point (y 0) (y 1)).const_mul _).smul (hf.continuousAt.tendsto.comp (hp.prodMk_nhds hq))

def overture (V:ropes Cover α α)(b:J⊆ S)(P:Gen (Pen D J) (Cloth α))(Q:Gen (Pen D (S\J)) (Cloth α))(r:ℕ): Ten (Pen D S) (Cloth α) r:=∑ i∈Finset.antidiagonal r, ruins (swivel (lakeL V b P Q r i.1 i.2))
def Sewing (V:ropes Cover α α)(b:J⊆ S)(P:Layers (Pen D J) (Cloth α))(Q:Layers (Pen D (S\J)) (Cloth α))(i j:ℕ): Gen (Pen D S) (Cloth α) := ∑ a∈Finset.antidiagonal i,∑ c∈Finset.antidiagonal j, overture V b (P a.1 c.1) (Q a.2 c.2)

lemma roseQ [Fintype α]{V:(n:Side)→ ropes (Site n) α α}{K:ropes Cover α α}(b:J⊆ S){P:(n:Side)→ Layers (Pen D J) (Site n×α)}{Q:(n:Side)→ Layers (Pen D (S\J)) (Site n×α)}{X:Layers (Pen D J) (Cloth α)}{Y:Layers (Pen D (S\J)) (Cloth α)}(t:Pilots V K)(p:∀ l ≤ i,∀ e ≤ j,∀ r, Bends 0 (fun n=> P n l e r) (X l e r))(q:∀ l ≤ i,∀ e ≤ j,∀ r,Bends 0 (fun n=>Q n l e r) (Y l e r))(r):
      Bends 0 (fun n=>sewsV (V n) b (P n) (Q n) i j r) (Sewing K b X Y i j r):=by
   apply leaderT; intro a ha; apply leaderT; intro c hc; have ht:=Finset.mem_antidiagonal.mp ha; have hv:= Finset.mem_antidiagonal.mp hc
   simp_rw [←lakeReads]; exact anzas (P:=fun (z:ℕ×ℕ) n=> refuge (swivel (lakeL (V n) b (P n a.1 c.1) (Q n a.2 c.2) r z.1 z.2))) _ (fun y hy=>(dawnB b t (p _ (by omega) _ (by omega) (y.1+1)) (q _ (by omega) _ (by omega) (y.2+1)) (Finset.mem_antidiagonal.mp hy)).swiveled.rest)
end YM.WilsonCoeffUV.Wheel.Mark
