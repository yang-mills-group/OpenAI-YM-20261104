import YM.OPE.Compatible.Harks.Will
/-!
# layers of paid small initial/correction directions
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
variable {d k:ℕ}{G:ℕ→Type}[∀ i,NormedAddCommGroup (G i)][∀ i,NormedSpace ℝ (G i)]
variable {μ:ℕ→ℝ}{T:Cuts d μ t x E G}
variable [∀ i,CompleteSpace (G i)]
lemma even (T:Cuts d μ t x E G)(hr:t<r)(hx:∀ i:ℕ,i<d→μ i≠r):∀ i:ℕ,i ≤ d → (∀ j:ℕ,i≤ j→j<d→ μ j<r) → ∃ C:ℝ,0≤C ∧ ∀ p:ℕ→ E→L[ℝ] E,(∀ i,Grooved T (p i))→∀ a:ℕ→ E,Run p a 0→ a 0∈ T.flag i→Hex r a (C*‖a 0‖):=by
    intro i hi; induction hi using Nat.decreasingInduction with
    | self =>
         refine fun _=>⟨1,zero_le_one,fun p hp a ha hx=>?_⟩; rw [one_mul]; refine Run.gap hr _ T.fast ?_ (Hex.zero E r) ha (fun i=> (hp i).march _ (Run.hero ha hp le_rfl hx i)) le_rfl; simp [norm_nonneg]
    | of_succ k hj H=>
         intro hk; obtain ⟨c,hc,H⟩:= H (fun j hJ=> hk j (by omega)); obtain ⟨B,Hb,hB⟩:=solk T hr hx (k+1) (by omega); let L:=T.lift k hj; let A:=T.Tap k; let q:= ‖L‖ * ‖A‖; have hq:0≤q:=mul_nonneg (norm_nonneg _) (norm_nonneg _); have he':0≤r:=T.fast.trans hr.le; let D:= (max 0 x+r)*q; have hd:0≤ D:=by unfold D; positivity
         let V:=q+B*D; have hv:0≤ V:=by unfold V; positivity
         refine ⟨V+c*(1+V),by positivity,fun p hp a ha he=>?_⟩; let v:= fun i=> A (a i); let z:= fun i=>L (v i); have hf:Hex r v ‖A (a 0)‖:= scalarHexu (Run.tap ha hp hj he) (T.tempo _ hj).le (hk k le_rfl hj).le; have hh':Hex r z (q*‖a 0‖):=(Hex.invoke L hf).tips he' (by unfold q; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (le_opNorm ..) (norm_nonneg _))
         let g:= fun i=> p i (z i)-z (i+1); have hF(n):z n∈ T.flag k ∧ T.Tap k (z n)=v n:=T.rises ..; have hx':∀ i,g i∈ T.flag (k+1):=by
              intro i; apply (T.next k hj _).2; refine ⟨(T.flag _).sub_mem ((hp i).leaves k hj.le _ (hF i).1) (hF _).1,?_⟩; unfold g; rw [map_sub,(hp i).tempo k hj (z i) (hF i).1,(hF i).2,(hF (i+1)).2]; rw [show v (i+1)= μ k • v i+0 from Run.tap ha hp hj he i,add_zero,sub_self]
         have hg:Hex r g (D*‖a 0‖):= (show Hex r g _ from (hh'.pays p (fun i=> (hp i).cap.trans (le_max_right ..))).sub hh'.forward).tips he' (le_of_eq (by unfold D; ring)); obtain ⟨w,Hw,Hg⟩:= hB p hp g _ hg hx'; let Y:=race p g w; have hz:Run p (z+Y) 0:=by
              intro i; rw [Pi.add_apply,Pi.add_apply,map_add]; erw [Pi.zero_apply,add_zero]; rw [show Y (i+1)=p i (Y i)+(p i (z i)-z (i+1)) from gait p g w i]; abel
         have hc' : Hex r (z+Y) (V*‖a 0‖):=(hh'.add Hg).tips he' (le_of_eq (by unfold V; ring)); let u:=a-(z+Y); have hm:(z+Y) 0∈ T.flag k:=(T.flag k).add_mem (hF 0).1 ((T.next k hj _).1 Hw).1
         have hm':u 0∈T.flag (k+1):=by refine (T.next k hj _).mpr ⟨(T.flag k).sub_mem he hm,?_⟩; change T.Tap _ (a _- (z 0+w))=0; rw [map_sub,map_add,(hF 0).2,((T.next k hj w).1 Hw).2,add_zero]; exact sub_self _
         have hh:= H p hp u (sub_zero (0:ℕ→E) ▸ Run.sub ha hz) hm'
         have hN: ‖u 0‖≤ (1+V)*‖a 0‖ := (norm_sub_le ..).trans ((add_le_add_right (show ‖(z+Y) 0‖≤ V*‖a 0‖ from by simpa only [pow_zero,mul_one] using hc' 0) ‖a 0‖).trans_eq (show _= (1+V)*‖a 0‖ from by ring))
         apply (show Hex r a _ from (show u+ (z+Y)= a from sub_add_cancel ..) ▸ hh.add hc') |>.tips he'
         calc _ ≤ c*((1+V)*‖a 0‖)+V*‖a 0‖:= add_le_add_left (mul_le_mul_of_nonneg_left hN hc) _
              _= _:=by ring
structure ShadeR (T:Cuts d μ t x E G)(k:ℕ)(r:ℝ):Prop where
   Fast : t<r
   slot : k≤d
   slow (j:ℕ)(h:j < k) : r < μ j
   brisk (j:ℕ)(h:k≤j)(hh:j<d): μ j<r
omit [∀ i,CompleteSpace (G i)] in
lemma ShadeR.ex (h:ShadeR T k r):∀ i:ℕ,i<d→ μ i≠r:=fun i hi=>by by_cases hx:i<k; exact (h.slow _ hx).ne'; exact (h.brisk _ (Nat.le_of_not_gt hx) hi).ne
lemma CutR (T:Cuts d μ t x E G) {R:ℝ}(hr:ShadeR T k r)(hR:ShadeR T k R)(he:r≤ R) :∃ C:ℝ,0≤C ∧ ∀ p:ℕ→ E→L[ℝ] E,(∀ i,Grooved T (p i))→∀ a f:ℕ→E,∀ b x:ℝ,Hex r f x→ Run p a f→ Hex R a b→Hex r a (C*(‖a 0‖+x)):=by
     obtain ⟨c,hc,H⟩:=even T hr.Fast hr.ex k hr.slot hr.brisk; obtain ⟨D,hD,t⟩:= solk T hr.Fast hr.ex 0 (by omega); refine ⟨(1+D)*c+D,by positivity,fun p hp a f b x ha ht hh=>?_⟩; obtain ⟨v,_,hF⟩:= t p hp f x ha (fun i=> T.first _); let g:=race p f v; have hv:Run p g f:=gait p f v
     have he':0≤r:= T.fast.trans hr.Fast.le; have hu:Run p (a-g) 0:=sub_self f ▸ Run.sub ht hv; have hg:= H p hp _ hu (inLayer hR.Fast hp hu hR.slot hR.slow (hh.sub (hF.warm he' he))); have hy:= ha.price; apply (show Hex r a _ from (show a-g+g= a from sub_add_cancel ..) ▸ hg.add hF)|>.tips he'
     have hs : ‖g 0‖≤ D*x:= (show _ from by simpa [g] using hF 0); refine ((add_le_add_left (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add_right hs ‖a 0‖)) hc) (D*x))).trans ?_; nlinarith only [show 0 ≤ D*c*‖a 0‖ from by positivity, show 0 ≤ c*x from by positivity,show 0 ≤ D*‖a 0‖ from by positivity]
end YM.OPE.Hark
