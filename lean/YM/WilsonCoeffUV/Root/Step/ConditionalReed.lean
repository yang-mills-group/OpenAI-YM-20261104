import YM.WilsonCoeffUV.Thermo.Context
import YM.WilsonCoeffUV.Root.Step.WickThermo
import YM.WilsonCoeffUV.Root.Step.InverseClock
/-!
# Bul with pivot. Engineering weight d belongs to column family horizon h,
protocol's time cut l is fixed for all columns at their announced horizon.
Input already translated *within* every preimage. Output here prior coupling
reset and projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
open scoped Topology BigOperators
variable {n:Side}{U α β V ι E : Type*}{k r l j:ℕ} {A B C D X Y σ η : ℝ}{p:Cover}
variable [NormedAddCommGroup V][NormedSpace ℝ V]
section
variable (u:U ≃ α)[Fintype U][Fintype α]
lemma sprint (G:Matrix U U ℝ)(K:Layers ℝ U)(P:ℕ→Gen V U)(h e): bend u (bul G K P h e)=bul (allotM u u G) (fun x y=>bend u (K x y)) (fun y=> bend u (P y)) h e:=by
    let M:= allotM u u G; let Y x y:=bend u (K x y); let L i:=bend u (P i)
    induction h using Nat.strong_induction_on generalizing e with
    | h n ih=>
       cases n with
       | zero=> rw [bul_zero,bul_zero]
       | succ n=>
          have hv (A:Matrix U U ℝ)(e): bend u (ravel A K (bul G K P) n e)=ravel (allotM u u A) Y (bul M Y L) n e:= by
             rw [bend_ravel]; exact ravel_eq _ _ _ _ _ (fun _ _ _ _=>rfl) (fun i hi j _=> ih i (by omega) j)
          change bend u _=bul M Y L (n+1) e; rw [bul_next,bend_smul,bend_add,bend_add,bend_ripple,hv,hv, ih n n.lt_succ_self, bul_next]; rfl
omit [Fintype α] in
lemma capit {R:(n:Side)→ ropes (Site n) α α}{F:ropes Cover α α}(h:Pilots R F): Pilots (fun n=>(R n).transpose) F.transpose:= by
    obtain ⟨s,c,hp,H⟩:=h.fees; refine ⟨fun x y=> h.point y x,h.move.mono (fun n hn b x y=> hn b y x),s,c,hp,H.mono (fun n hn=>⟨hn.1,fun x y=>?_⟩)⟩
    rw [(tor n).swap]; exact hn.2 ..
end
section
variable [Fintype α]
def paintC (G:ropes Cover α α)(K:Layers ℝ (Cloth α))(P:Layers V (Cloth α))(h e:ℕ): Gen V (Cloth α):= ∑ i∈Finset.antidiagonal h,∑ j∈Finset.antidiagonal e, rondel G (K i.1 j.1) (P i.2 j.2)
noncomputable def heap (G:ropes Cover α α)(K:Layers ℝ (Cloth α))(P:ℕ→Gen V (Cloth α))(h e:ℕ): Gen V (Cloth α):= match h with
| 0=> P e
| k+1=> ((k+1:ℕ):ℝ)⁻¹ • (rime G (heap G K P k e)+paintC G K (fun j i=> if _h:j≤k then heap G K P j i else 0) k e + paintC G.transpose K (fun j i=> if _h:j≤k then heap G K P j i else 0) k e)
termination_by h
omit [Fintype α] in
lemma level (G:ropes Cover α α)(K:Layers ℝ (Cloth α))(P:ℕ→ Gen V (Cloth α))(e):heap G K P 0 e=P e:=by rw [heap]
omit [Fintype α] in
lemma inchC (G:ropes Cover α α)(K:Layers ℝ (Cloth α))(P:ℕ→ Gen V (Cloth α))(k e):heap G K P (k+1) e=((k+1:ℕ):ℝ)⁻¹ • (rime G (heap G K P k e)+paintC G K (heap G K P) k e+ paintC G.transpose K (heap G K P) k e):=by
   have he (g:ropes Cover α α): paintC g K (fun j i=> if _a:j≤k then heap G K P j i else 0) k e=paintC g K (heap G K P) k e:= by
      apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj; dsimp only; rw [dif_pos (by have he:=Finset.mem_antidiagonal.mp hi; omega)]
   rw [heap,he,he]
variable [CompleteSpace V]
lemma spans_bracket {Q:(n:Side)→ Layers ℝ (Co n α)}{P:(n:Side)→Layers V (Co n α)}{K:Layers ℝ (Cloth α)}{R:Layers V (Cloth α)}{T:(n:Side)→ ropes (Site n) α α}{G:ropes Cover α α}(h:Pilots T G){v e:ℕ}(g:∀ h≤v,∀ i≤e,∀ r, Yields (fun n=>Q n h i r) (K h i r))(f:∀ h≤v, ∀ i≤e,∀ r, Bends p (fun n=>P n h i r) (R h i r))(r):
    Bends p (fun n=>ravel (T n) (Q n) (P n) v e r) (paintC G K R v e r):=by
   apply leaderT; intro j hj; apply leaderT; intro i hi
   have hp:=Finset.mem_antidiagonal.mp hj; have ht:= Finset.mem_antidiagonal.mp hi; exact rondel_period h (fun _ _=>g _ (by omega) _ (by omega) _) (fun _ _=> f _ (by omega) _ (by omega) _)
lemma heap_period {Q:(n:Side)→ Layers ℝ (Co n α)}{P:(n:Side)→Pal V (Co n α)}{K:Layers ℝ (Cloth α)}{R:Pal V (Cloth α)}{T:(n:Side)→ ropes (Site n) α α}{G:ropes Cover α α}(h:Pilots T G)(e:∀ i j r,Yields (fun n=> Q n i j r) (K i j r))(p':∀ i r,Bends p (fun n=>P n i r) (R i r))(v f r):
    Bends p (fun n=>bul (T n) (Q n) (P n) v f r) (heap G K R v f r):=by
    induction v using Nat.strong_induction_on generalizing f r with
    | h n ih=>
       cases n with
       | zero=> simp_rw [bul_zero, level]; apply p'
       | succ n=>
         simp_rw [bul_next,inchC]; have hu {M A} (z:Pilots M (A:ropes Cover α α)):= spans_bracket (P:=fun m=> bul (T m) (Q m) (P m)) (Q:=Q) (R:=heap G K R) (K:=K) z (v:=n) (e:=f) (fun h _ i _ r=> e h i r) (fun i hi j _ r=> ih i (by omega) j r) r
         exact (((rime_period h (ih n n.lt_succ_self f (r+2))).add (hu h)).add (hu (capit h))).μ _
end
omit [NormedSpace ℝ V] in
lemma cork_scoop {U:Type*}{p:U}{F:Ten V (U×(α⊕β)) r}{d:Distance U}(h:Cork d p σ A F): Cork d p σ A (scoop F):=⟨h.1,fun x=> h.2 (pierR ∘ x)⟩
omit [NormedSpace ℝ V] in
lemma Bends.scooped {P:raw (α⊕β) V r}{F}(h:Bends p P F): Bends p (fun n=> scoop (P n)) (scoop F):=by
    obtain ⟨s,a,ht,H⟩:=h.price; exact ⟨fun x=>h.point (pierR ∘ x),s,a,ht,H.mono (fun _ hn=> cork_scoop hn)⟩
section
open Embroider Precision
variable {G:Gauge} (P:Patch)(K:KernelChoices)(Ñ:ChartRatio G) (Γ:ropes Cover (Larvae G P.L) (Larvae G P.L)) (M:ropes Cover (Larvae G P.L) (Hooks G)) (W:Canvas G)
variable {D:ℕ}
def slidesJ (M:ropes Cover (Larvae G P.L) (Hooks G))(p:Pal V (YForest G)): Pal V (Cloth (Hinge G P.L)):= fun i=> Bank.prism (upper 1 M) (tiles P.L (p i))
def puck (p:Pal V (YForest G)):= heap (stair (upper (β:=Hooks G) Γ 0) 0) (spurs P K Ñ Γ M W) (slidesJ P M p)
def windsT (l:ℕ)(p:Pal V (YForest G)): Pal V (YForest G):= fun i=> sluice (∑ j∈Finset.range (1+l+3*i), puck P K Ñ Γ M W p j i)
def gatherT {U:Type}[AddGroup U]{W:Type*}(w:Site P.L)(p:U)(F:Pal (Vote D) (U× W)): Pal (Vote D) (U×W):= fun i r=> (soprano P w D) ∘ revolve p (F i r)
def chorus (h:ℕ)(p:Pal (Vote D) (YForest G)): Pal (Vote D) (YForest G):= ((P.L.val:ℝ)^h / (P.L.val:ℝ)^4) • ∑ w:Site P.L, windsT P K Ñ Γ M W h (gatherT P w (lift w) p)
variable [CompleteSpace V]
lemma river (b:P.Branches K G)(t:LocalRatio Ñ){H Q} (g:PaintKit P K G H Q Γ M){F:Crude G}(e:∀ i r,Yields (fun n=> F n i r) (W i r))(l:ℕ)(w:Site P.L){p:Pal V (YForest G)}{U:(n:Side)→Pal V (Woods G n)}(x:∀ i r,Bends (lift w) (fun n=>U n i r) (p i r))(i r):
    Bends 0 (fun n=> reed (stepAt P K n) (xree P K n) H (Q n) Ñ (F (n*P.L)) l (U (n*P.L)) i r) (windsT P K Ñ Γ M W l p i r) :=by
   let s n:=stepAt P K n; let T n:=weaveH (ratioN P.L n) G; let I n:= weaveFine (ratioN P.L n) G; let O n:= xree P K n
   let Y (n:Side) j t:= bend (T n) (xray (s n) (O n) H (Q n) Ñ (F (n*P.L)) j t)
   let X (n:Side) := allotM (T n) (T n) (fillSlots (Woods G n) (mer (G:=G) P K H n))
   let Z (n:Side) i:= bend (T n) (srCold (U (n*P.L)) (teller G P K Q n) i)
   have he i r : Bends 0 (fun n=> Z n i r) (slidesJ P M p i r):=by
      apply Bends.congr (solo_flash (P:=tiles P.L (p i)) (Q:=fun n=>bend (I n) (U (n*P.L) i)) (Pilots.one.deck g.mark) ((x i r).ciphers w))
      refine Eventually.of_forall fun n=>?_ ; unfold Z srCold; rw [bend_fade (I n) (T n), show allotM (I n) (T n) _=upper 1 _ from cam_chart _ _]
   have hv : Pilots X (stair (α:=Larvae G P.L) (β:=Hooks G) (upper Γ 0) 0):=by
      rw [show X=fun n:Side=> stair (upper (allotM (I n) (I n) (mer (G:=G) P K H n)) (β:=Hooks G) 0) (β:=Hooks G) 0 from funext fun n=>lamp_chart ..]; exact ((g.toll.deck (Pilots.silent (β:=Hooks G))).deck' (Pilots.silent (α:=Hooks G)))
   let V n j:=bend (T n) (srShade (s n) (O n) H (Q n) Ñ (F (n*P.L)) (U (n*P.L)) j i)
   have hf j:Bends 0 (fun n=> V n j r) (puck P K Ñ Γ M W p j i r):=(heap_period (Q:=Y) (P:=Z) hv (spurs_enter P K Ñ H F Q b t e g) he j i r).congr (Eventually.of_forall fun n=> congr_fun (show V n j=_ from sprint ..).symm _)
   refine (leaderT (s:=Finset.range (1+l+3*i)) (P:=V) (F:=fun j=> puck P K Ñ Γ M W p j i) (fun i _=> hf i)).scooped.congr (Eventually.of_forall fun n=>?_)
   rw [reed, into_shade (ratioN P.L n), bend_sum]; rfl
end
end YM.WilsonCoeffUV.Soil
