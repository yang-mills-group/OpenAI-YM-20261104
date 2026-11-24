import YM.OPE.Compatible.Plains.Coax
/-! # Asserting Negative Heat. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open MeasureTheory Function Set Topology Filter
open Silt Libra Shrew PertExtension Series GaussianScore Flock
open scoped Topology BigOperators Classical ContDiff
variable {I J E F:Type}[Fintype J][LinearOrder I]
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable [MeasurableSpace F][BorelSpace F](μ:Measure F)[μ.IsAddHaarMeasure](A:Law F)
open Finset
lemma sing_after (Z:F→L[ℝ] E)(L:I→Module.Dual ℝ E)(x:E)(s:Finset I):
 let F(i:I):= L i ∘ₗ Z.toLinearMap
 A.average μ (fun y=>fauna (fun i j=>A.wick (F i) (F j)) L s (x+Z y))=∏ i∈s, L i x:=by
   intro f; let K(i j):=A.wick (f i) (f j); let U:=fun y=> x+Z y; let S(s:Finset I):=fauna K L s; let g(s: Finset I):= S s ∘ U
   have hp(v:Finset I):Bond (g v):=stayBond Z (incense ..) x
   change A.average μ (g s)= _; induction s using Finset.strongInduction with | _ s ih
   obtain rfl|hh:=s.eq_empty_or_nonempty; · unfold g S; rw [fanE,Finset.prod_empty]; exact Law.empty ..
   let a:=s.min' hh; let v:=s.erase a; have ht:=innerA hh
   let Y:=A.inverse (f a); have hz: g s=L a x • g v+ (⇑(f a)* g v-∑ i∈v, K a i • g (v.erase i)):=by
       funext z; unfold g S; rw [Function.comp_apply,pier K L ht]; simp only [Pi.add_apply,Pi.sub_apply, Pi.smul_apply,Pi.mul_apply,Finset.sum_apply,Function.comp_apply,v, U,map_add]; change _= L a x* _ + (L a (Z z)*_-_); unfold a; ring
   have he : poke Y (g v)= ∑ i∈v, K a i • g (v.erase i):=by
       let H:= fauna K L v
       rw [show (∑ i∈v,K a i • g (v.erase i))= poke (Z Y) H ∘ U from ?_]; swap
       · rw [show _= _ from poHer K L (Z Y) v]; funext i; rw [Function.comp_apply,Finset.sum_apply, Finset.sum_apply]; exact sum_congr rfl fun i _=>rfl
       funext z; unfold poke; change fderiv ℝ (H ∘ U) z Y= _; have hh: fderiv ℝ U z =Z:=by
          have hv:= Z.hasFDerivAt (x:=z); let T:=((hasFDerivAt_const x z)).add hv; exact T.fderiv.trans (zero_add Z)
       rw [fderiv_comp z (show DifferentiableAt ℝ H _ from (incense K L v).smooth.differentiable (by simp) (U z)) (show DifferentiableAt ℝ U z from by unfold U; fun_prop), hh];rfl
   rw [hz, ← he]; have hv:= (hp v).amount Y; change Bond (poke Y (g v)) at hv; rw [sun μ A ((hp v).scale _) (((Bond.glyph (f a)).mul (hp v)).sub hv),snow μ A ((Bond.glyph _).mul (hp v)) hv, show (A.average μ (⇑(f a)*g v))=_ from (by rw [show f a=A.P Y from (A.applies _).symm]; exact IP μ A Y (hp v) : A.average μ (⇑(f a)*g v)=A.average μ (poke Y (g v))),sub_self,add_zero,scooted,ih _ (Finset.erase_ssubset ht.1)]; exact Finset.mul_prod_erase s (fun i=>L i x) ht.1
lemma heaters {e:ℕ}(Z:F→L[ℝ] PAD J)(p:Song (PAD J))(hp:p∈ harmon (PAD J) e)(g:PAD J→ℝ)(h:Bond g)(hh:∀ x:PAD J,A.average μ (fun y=> g (x+Z y))= Strike e p x):
     Strike e (fixExp (opus (chamber A Z)) (-(1/2:ℝ)) e p)=g:=by
         let H:=fixExp (opus (chamber A Z)) (-(1/2:ℝ)) e p
         have hv:Bond (Strike e H):= Bond.sum _ _ (fun i _=> Bond.multiline (w:=fun (_:Fin i)=>fun (x:PAD J)=>x) (H i) (fun _ _=>Bond.glyph _))
         apply inject_chant μ A Z hv h; intro x; specialize hh x; rw [hh]; convert! (basisH μ A Z x 1 H (peak _ _ _ _ hp)) using 1; simp; unfold H; rw [one_pow,← switching]; rw [negatives (by simpa only [one_smul] using opusReducer (chamber A Z) 1) p hp (1/2) _ le_rfl]
end YM.OPE.Prairies
