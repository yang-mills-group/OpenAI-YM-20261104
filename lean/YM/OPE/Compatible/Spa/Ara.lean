import YM.OPE.Compatible.Spa.Fen
/-!
# Flag ledger. compressed.P
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter Finset
open Drift
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Fin d→Type}{M E F Q:Type}{v:ℝ}{t p:M→ℝ}{ρ:ℝ}
variable [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
-- `read F→ Tokens`. Lift provided ζ.Price. specific Veins inputs
variable {A:ℕ→ M→Submodule ℝ E}{Y:M→ Submodule ℝ E}{X:(e:Fin d)→(m:M)→ A e.val m→ₗ[ℝ] Jewel (V e)}{g:E→ₗ[ℝ] E}{R:(e:Fin d)→(m:M)→ Jewel (V e)→ₗ[ℝ] A e.val m}
namespace Pipes
variable (H:Pipes A Y X g R)
include H
omit H
omit [NormedSpace ℝ E] in lemma growth {q:Q→M} {f:M→ E}(h:Wealth f t p): Wealth (f∘q) (t ∘ q) (p ∘q):=by obtain ⟨v,hv,k,H⟩:=h; exact ⟨v,hv,k,fun i=> H _⟩
variable [∀ i,FiniteDimensional ℝ (V i)]
include H
structure Charge (H:Pipes A Y X g R)(p:M→ℝ):Prop where
      keep : 1 ≤ p
      sent (e:Fin d): Wealth (fun i=> ((A e.val i|>.subtype).comp (R e i)).toContinuousLinearMap) p 1
      fare(e:Fin d) (Q:Type) (f:Q→ M) (b:Q→ℝ)(x:(i:Q)→ A e.val (f i))(h:Wealth (fun i=>(x i).val) (p∘f) b):Wealth (fun i=> X e (f i) (x i)) (p ∘f) b
      buys(e:Fin d)(Q:Type)(f:Q→M)(b:Q→ℝ)(hq:0 ≤ b)(x:(i:Q)→ A e.val (f i))(h:Wealth (fun i=>(x i).val) (p∘f) b)(he:∀ i,X e (f i) (x i)=0):∃ y:(i:Q)→ A (e.val+1) (f i),Wealth (fun i=>(y i).val) (p∘f) b∧∀ i,(x i).val-(y i).val∈ Y (f i)
variable {H} (h:Charge H p)
include h in lemma Charge.blu {Q:Type} (e:Fin d)(f:Q→M)(b:Q→ℝ)(x:Q→ Jewel (V e))(hp:Wealth x (p∘f) b): Wealth (fun i=>(R e (f i) (x i)).val) (p∘f) b:= one_mul b ▸ wealth_mul (growth (q:=f) (h.sent e)) hp (fun i=>(((A e.val (f i)).subtype.comp (R e (f i))).toContinuousLinearMap).le_opNorm (x i))
include h
lemma jPort (f:Q→M)(b:Q→ℝ)(hb:0 ≤ b) (v:ℕ)(hv:v≤d):∀ x:(i:Q)→A v (f i),Wealth (fun i=>(x i).val) (p∘f) b→Wealth (fun i=> H.port (f i) (x i).val) (p∘f) b:=by
      have hY: 1 ≤ p∘f:= fun i=> h.keep _
      induction hv using Nat.decreasingInduction with
      | self=> intro x hx; simp_rw [fun i=>(H.worthM (f i)|>.hero (x i).val).1 (le_sup_left (a:=A d (f i)) (x i).property)]; exact wealthZ ..
      | of_succ i hi IH=>
          intro x hx; let s:Fin d:=⟨i,hi⟩; let y(j):= X s (f j) (x j); have hy:= h.fare s Q f b x hx; let z(j):= R s (f j) (y j); have hh:Wealth (fun i'=>(x i'-z i').val) (p∘f) b:= subW hY hb hx (h.blu s f b y hy); have hk(j):X s (f j) (x j-z j)=0:=by rw [map_sub,show X s (f j) (z j)= y j from H.toll ..]; exact sub_self _
          obtain ⟨u,hu,hU⟩:= h.buys s Q f b hb (fun j=> x j-z j) hh hk; have he(j): H.port (f j) (x j).val= Pi.single s (y j)+ H.port (f j) (u j).val :=by
               have hp: (x j-z j).val-(u j).val∈ Bay A Y d (f j):=le_sup_right (a:=A d (f j)) (hU j); have he:= (H.worthM (f j)|>.hero _).1 hp; rw [sub_eq_zero.mp (show H.port _ (x j-z j).val-H.port _ (u j).val=0 from (by rw[←map_sub];exact he))|>.symm]; erw [map_sub]; rw [show (z j).val=bulk R (f j) (Pi.single s (y j)) from (bulk_single ..).symm,H.worthM _|>.len]; abel
          simp_rw[he]; exact anthW hY hb (aimW (ContinuousLinearMap.single ℝ (fun i=> Jewel (V i)) s) hy) (IH u hu)
lemma φWorth (f:Q→M)(b:Q→ℝ)(hb:0 ≤ b)(x:Q→ E)(hx:Wealth x (p∘f) b): Wealth (fun i=> H.port (f i) (x i)) (p∘f) b:= jPort h f b hb 0 (Nat.zero_le _) (fun i=>⟨x i, H.top _|>.symm ▸ Submodule.mem_top⟩) hx
-- obtains op bound from tests linear
lemma wZenith {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](L:M→ E→ₗ[ℝ] F)(hp:∀ (Q:Type)(f:Q→M)(b:Q→ℝ)(x:Q→ E),0 ≤ b→ Wealth x (p ∘ f) b→ Wealth (fun j=> L (f j) (x j)) (p ∘ f) b): ∃ U:M→ E→L[ℝ] F, Wealth U p 1 ∧∀ i,(U i).toLinearMap=L i:=by
      let a(j:M× E):= ‖j.2‖; let v:M×E→ M:=Prod.fst; obtain ⟨C,hc,k,hK⟩:=hp (M×E) v a Prod.snd (fun i=>norm_nonneg _) (show Wealth (Prod.snd (α:=M) (β:=E)) (p∘v) a from ⟨1,zero_le_one,0,fun i=>by rw [pow_zero,mul_one,one_mul]⟩)
      have hh(i:M)(x:E): ‖L i x‖≤ C*(p i)^k*‖x‖:= hK (i,x); refine ⟨fun i=> LinearMap.mkContinuous (L i) _ (hh i),⟨C,hc,k,fun i=>?_⟩,fun _=>rfl⟩; rw [Pi.one_apply,mul_one]; exact ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc (pow_nonneg (le_trans zero_le_one (h.keep i)) _)) (hh i)
lemma Charge.CLt : ∃ U:M→ E→L[ℝ] Mel V, Wealth U p 1 ∧∀ i,(U i).toLinearMap=H.port i:= wZenith h _ (fun _ f b x hb hx=> φWorth h f b hb x hx)
end Pipes
end YM.OPE.Hark
