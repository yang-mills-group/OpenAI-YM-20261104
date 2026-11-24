import YM.WilsonCoeffUV.Wick.Filter
/-!
# Wick matrices and zeroth exact step
Rotation/projection separate. Equality in native spaces. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Soil Cosmos
open Exterior Next.Free Tree Precision Power Embroider
open scoped Topology BigOperators ContDiff
variable {c f n:Side}{U V W α β: Type*} {r e j k m D N:ℕ}{G:Gauge}{x s ξ σ A' B:ℝ}
lemma chipV {P: Gen (Vote D) U}(h:still P k)(v:Volume D): still (cloaks (ContinuousLinearMap.apply ℝ ℝ v).toLinearMap P) k:=fun i hi=>by rw [cloak_e,h i hi,map_zero]
lemma moss (h:s>0){P:Ten (Vote D) (YForest G) r}(p:Cork Bank.terrain 0 s A' P)(v:Volume D) (n:Side): plume (tinct (ContinuousLinearMap.apply ℝ ℝ v).toLinearMap P) n=tinct (ContinuousLinearMap.apply ℝ ℝ v).toLinearMap (plume P n):= by
    let f:=ContinuousLinearMap.apply ℝ ℝ v; funext x; change _=f _; rw [plume,plume,f.map_tsum (creased p h n x)]; apply tsum_congr; intro i; unfold peglet; split; rfl; exact (map_zero f).symm
lemma plume_shift {α:Type} (v: Cover){P: Ten ℝ (Cloth α) r}(n:Side): plume (revolve v P) n= revolve (wrap n v) (plume P n):= by
    classical
    let B: Equiv.Perm (dock Cover α r) := (Equiv.refl (Fin r)).arrowCongr (jog v); funext x; rw [plume,← B.tsum_eq]; unfold revolve plume
    apply tsum_congr; intro y; unfold peglet; change (if slideC n (jog v ∘ y)=x then P (jog (-v) ∘ (jog v ∘ y)) else 0)=(if slideC n y=jog (-wrap n v) ∘ x then P y else 0)
    have ht : slideC n (jog v ∘ y)=jog (wrap n v) ∘ (slideC n y):= funext fun i=> fold_move n v (y i)
    have he{A W:Type}[AddGroup A](x:dock A W r)(p:A): jog (-p) ∘ (jog p ∘ x)=x:= by ext i <;> simp [jog]
    have hs: slideC n (jog v ∘ y)=x ↔ slideC n y=jog (-wrap n v) ∘ x :=⟨fun p=> by rw [← p,ht]; exact (he ..).symm,fun p=>by rw [ht,p]; simpa only [neg_neg] using (he x (-wrap n v))⟩
    split_ifs with hv hu hu; rw [he]; apply False.elim; exact hu (hs.mp hv); apply False.elim; exact hv (hs.mpr hu); rfl
lemma orientation_cork [NormedAddCommGroup V]{v:Cover}{P:Ten V (YForest G) r}(p:Cork Bank.terrain v s A' P) (ht:0<s): Cork Bank.terrain 0 s (A'*Real.exp (s*Bank.terrain.gap 0 v)) P:= by
   refine ⟨mul_nonneg p.1 (by positivity),fun x=> (p.2 x).trans ?_⟩; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ p.1; rw [← Real.exp_add]; apply Real.exp_monotone
   have he : (tread Bank.terrain 0 x:ℝ)≤ tread Bank.terrain v x+Bank.terrain.gap 0 v:= by exact_mod_cast (property_le 0 v x)
   linarith only [mul_le_mul_of_nonneg_left he ht.le]
lemma spinG0 (x b:Cover)(i:G.ColorIndex)(P:Ten ℝ (YForest G) (r+1)) (h:∀ v:Cover, windsL v i P=0) : windsL x i (revolve b P)=0:=by
   funext v
   change _=(0:ℝ)
   rw [show (0:ℝ)=windsL (-b+x) i P (jog (-b) ∘ v) from congr_fun (h _) _|>.symm]
   unfold windsL; simp_rw [Finset.sum_apply, Pi.sub_apply]; apply Finset.sum_congr rfl; intro j _
   unfold prune revolve; rw [← comps_head,← comps_head]
   rw [show jog (-b) (stone (x-step j,j) i)=stone ((-b+x-step j),j) i from (by simp [jog,stone,add_sub_assoc]),show jog (-b) (stone (x,j) i)=_ from rfl]
   all_goals rfl
section
variable (A:Levels G)(Ñ:ChartRatio G)(X: Single G D)
abbrev canonP (n:Side): Vell G n D:= fun i r=> plume (X i r) n
lemma cargo (h:shellK k X)(n:Side): shellK k (canonP X n):=by
    intro i j e; unfold canonP; rw [h i j e]; exact plume_zero _
lemma chore (p:∀ i,Pure (X i)) (i)(n:Side): Pure (canonP X n i):= fun r=> rounding n _ (p i r)
lemma pieces (p:Stakes X)(g:shellK k X)(e:∀ i r, Standby (X i r))  (v:Cover) (b:Volume D): NullTop (fun r=> revolve (wrap n v) (jot b (canonP X n) 0 r)):=by
   choose s a hS H using e; let Y:= jot b X; let u:=ContinuousLinearMap.apply ℝ ℝ b
   have he (r): jot b (canonP X n) 0 r= plume (Y 0 r) n:= Eq.symm (moss (hS 0 r) (H 0 r) b n)
   have hv: Pure (Y 0):=jot_code (W:=X) b (p.pur 0)
   simp_rw [he,←plume_shift v]; let T r:=revolve v (Y 0 r); apply curtainT T
   · intro r σ x; unfold T revolve; exact hv r σ (jog (-v) ∘ x)
   · refine ⟨k+1,fun i hi=>?_⟩; unfold T; rw [show Y 0 i=0 from (jot_length b g) _ _ (by omega)]; rfl
   · intro r; have he:= Cork.touch u (H 0 r); exact ⟨s 0 r,_,hS 0 r,orientation_cork (V:=ℝ) ((Cork.turn (P:=Y 0 r) v he)) (hS 0 r)⟩
   intro r x i; apply spinG0 x v _ _; intro j; funext h; have hx:= sky_split p.vert p.pur 0 r (by intro _ h; omega) j i; have hb := congr_fun hx h
   apply Eq.trans _ (show u ((windsL j i (X 0 (r+1))) h)=(0:ℝ) from by rw [hx];rfl)
   unfold windsL; simp_rw [Finset.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro k _; simp_rw [Pi.sub_apply,map_sub]; rfl
end
end YM.WilsonCoeffUV.Bank.Carp
