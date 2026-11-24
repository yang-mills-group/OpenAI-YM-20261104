import YM.WilsonCoeffUV.Marked.Paths.Determinism
import YM.WilsonCoeffUV.Marked.Capture.Draw
/-!
# Enroll re-expression fees on gauge-coupling stencil. FULL graded.
 Output preserves selected cover reps for any demand under REAL stamp meter.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Wheel Wheel.Mark Wheel.Express Embroider Address
open MeasureTheory
variable {G:Gauge}{n:Side}{k h r t i j l e m b:ℕ}{s v u t' A B:ℝ}
variable {V W I α β ι:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{S J: Finset I}{c:I}{o:Cover}{D:I→ℕ}
omit [NormedSpace ℝ V] in
lemma tenure_flex (P:Robes G V k)(p:I→ Cover)(h:tenure P S p c i s A)(qu:t'≤ s)(hx:A ≤ B): tenure P S p c i t' B:=by
    intro j u r
    refine cap_raise (Work.F08.budget_minor (h j u r) (fun i' => mul_nonneg (by positivity) (ink_pos _)) (fun i'=> ?_)) hx
    exact mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_right qu (by positivity))) (bend_in _ qu) (ink_pos _) (by positivity)
-- common forecast chooses both Cash and width. For future marks on the SAME dictionary.
structure Stigmata (G:Gauge)(b k e:ℕ)(s c u:ℝ):Prop where
   original : 0<s
   affordable : 0<c
   le_one : c≤ s
   tag : 1≤u
   singles {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](P:Bookend V G) (r j:ℕ)(A:ℝ): r ≤ k → j≤e → Nimbus r e P→ Rain P e s A→ Rains (automa P r j) j c (u*A) ∧ ∀ i< j,(baton (automa P r j) j).2 i=P i
   bursts (I:Type)(S:Finset I)(z:I→ Cover)(t:I)(m:ℕ){V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V](P:Era G V)(A:ℝ): S.card≤ b→ t∈S → m ≤ k→ Auth m P→ 0≤ A →(∀ i<e,∀ d,Wig Bank.terrain z s A S (P.2 i d)) → ∀ j≤e,
     let R:= sphere P m j t z
     Rains R j c (u*A*Real.exp (-s/2*realmSize S z)) ∧ tenure R S z t j c (u*A*Real.exp (-s/4*realmSize S z)) ∧ ∀ v< j,(baton R j).2 v=(shifted P (-z t)).2 v
lemma rootBill (G:Gauge)(b k e:ℕ)(p:0<s): ∃ t u:ℝ, Stigmata G b k e s t u:=by
    choose V C g hp c H using fun i:Fin (k+1)=> autoK G s e i.val p
    choose v D h hx d W using fun i:Fin (k+1)=> planet G b i.val e s p
    let F:= fun i=> min (V i) (v i); let L:=fun i=>max (C i) (D i)
    have hF i:0<F i:= lt_min (g i) (h i); let i₀:Fin (k+1):=0
    let t:=Finset.univ.inf' Finset.univ_nonempty F; let U:= Finset.univ.sup' Finset.univ_nonempty L
    have ht:0<t:= (Finset.lt_inf'_iff _).mpr (fun i _=> hF i)
    have ht' i:t≤ F i:=Finset.inf'_le _ (Finset.mem_univ _); have hu i:L i≤ U:=Finset.le_sup' _ (Finset.mem_univ _)
    refine ⟨t,U,p,ht, ((ht' i₀).trans (min_le_left ..)).trans (hp i₀),((c i₀).trans (le_max_left ..)).trans (hu i₀),?_,?_⟩
    · intro V' _ _ _ P r j A x y s u; let r':Fin (k+1):= ⟨r,by omega⟩; obtain ⟨p,h⟩:=H r' j y V' P A s u; exact ⟨p.slack ((ht' r').trans (min_le_left ..)) (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (hu r')) u.1),h⟩
    intro I S z o r V' _ _ _ P A f x y w a c j b; let r':Fin (k+1):= ⟨r,by omega⟩; obtain ⟨p,q,h⟩:=W r' V' P I S z o A w x f a c j b; have hv:(D r')*A≤ U*A:=mul_le_mul_of_nonneg_right ((le_max_right ..).trans (hu r')) a; have hx:t≤v r':=(ht' r').trans (min_le_right ..)
    exact ⟨p.slack hx (mul_le_mul_of_nonneg_right hv (by positivity)), tenure_flex _ _ q hx (mul_le_mul_of_nonneg_right hv (by positivity)),h⟩

-- true sum over roots. sum alias charge. include address payout.
def sprigs (S:Finset I)(o:I)[DecidableEq I](s:ℝ):= tiePay Unit (Fintype.card (S.erase o)) (s/8)*tiePay Unit 0 (s/8)
lemma sprigsPay (p:c∈ S)[DecidableEq I](x:Cover)(h:0<s): SumBudget (fun r: ↑(S.erase c)→ Cover=> Real.exp (-s/4*realmSize S (toe S c x r))) (sprigs S c s):=by
   let Y:=Fin 0→ Cloth Unit; let _ : Unique Y:=inferInstance; let B:= (Equiv.prodUnique (↑(S.erase c)→ Cover) Y); let V (q:Fence Unit S c 0) := Syn Bank.terrain (toe S c x q.1) S q.2; let T (q:Fence Unit S c 0): ℝ:=Real.exp (-(s/4)* V q); let F r:=Real.exp (-s/4*realmSize S (toe S c x r)); have he i: F (B i)= T i:=by
       have hz : realmSize S (toe S c x (B i))= V i:=by
         apply le_antisymm (nested_u (S:=S) (toe S c x i.1) i.2); unfold Syn; apply league_le; rintro (i|j) (p|q) <;> first | exact Fin.elim0 j | exact Fin.elim0 q | exact leg_le Bank.terrain (fun z:S=> toe S c x _ z.val) i p
       unfold F T; rw [hz, neg_div]
   exact cap_walk F T B he (sprig_both p x h 0)
-- Bulletin carrier type for addressed. Keep every slot font (can't infer minimal counts sum from testing on common centers).
end YM.WilsonCoeffUV.Mer.Rolls
