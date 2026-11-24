import YM.FormalBulk08.Hay.Tales

/-! Finite regulator identification with planning interface. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f n:Side}{S:StepData c f}(F:Forest S.ratio)
variable (u:S.Choices)(p:Clip)(R:PathData G)(A:ChartRatio G)
variable (Y:Bid.Dir G c→AxisChart G F)(H:Critical F p R Y)(hr:LocalRatio A)
   (T: Hull (Pine G S F) (wire G c))
include H hr
lemma waxed : paste (Real.log ∘ heatS F A Y)= dish (motor (summit F Y)) (unmixed _) (halo (sap F A) (wire G c))+covelog (gauche (motor (summit F Y)) 1) := by
   let f:=summit F Y; have hm:=summit_score F p R Y H; have hh:= summit_zero F p R Y H;have hs: ContDiffAt ℝ ∞ f 0:=(summit_pay F p R Y H).of_le le_top
   have hx:= sap_smooth F A hr; have hP:coeff 0 (paste (sap F A))=1:= by rw [paste_first,sap_root F A hr,map_one]
   unfold Jets.halo; rw [pose, show roam ℝ _ (covelog _)=_ from change_covelog (insertAt ℝ (motor f)) hP]
   have hJ:gauche (motor f) 1=paste (fun x=> (dollars f x).det):= by rw [gauche,Matrix.det_one,map_one,map_one,one_mul,rent _ hh hs]
   have he: coeff 0 (roam ℝ (motor f) (paste (sap F A)))=1:= rode hP
   have ha: coeff 0 (gauche (motor f) 1)=1:= gauche_unit (motor f) (dollars f 0) 1 (inlay f) (by rw [mul_one]; exact hm)
   change _=covelog (roam ℝ (motor f) (paste (sap F A)))+covelog (gauche (motor f) 1); rw [←veil _ _ he ha,hJ,pin_rung _ (heat_zero F p R A Y H hr) (heat_cost F p R A Y H hr)]
   have hv : paste (heatS F A Y)=paste (sap F A ∘ f)*paste (fun x:Rot F G=> (dollars f x).det):= by rw [←paste_mul (sap F A ∘ f) _ ((show ContDiffAt ℝ ∞ _ (f 0) from (show f 0=0 from hh).symm ▸ hx).comp 0 hs) (merch f hs)]; exact paste_replace (tender F p R A Y H hr)
   rw [hv, paste_steps (sap F A) f hx hs hh]
variable (hG:G.Simple)(hS:S.patch.Branches S.kernel G){σ K B:ℝ}(hp:R.Bounds p σ K B)
include hG hS hp
lemma pealed : ∃ y,Elan (originH T.saddle (pending F u p R Y)) T (baseP (pending F u p R Y) (wambu F R A Y)) (flush F u A (novel p R f)) (unmixed (wire G c)) (unmixed (wire G c)) y 1 1:= by
    have he:=inlay (summit F Y); rw [summit_score F p R Y H] at he; let D:=pending F u p R Y; let W:=wambu F R A Y
    let T':=originH T.saddle D
    have ht: dish (still (Pine G S F) (wire G c)) (unmixed (wire G c)) (baseP D W)=dish (motor (summit F Y)) (unmixed (wire G c)) (flush F u A (novel p R f))+covelog (gauche (motor (summit F Y)) 1):= by
       rw [dish_id, flush,map_add, pending_tie F u p R Y H hG hp hS];
       unfold baseP W wambu; have hv:=heat_cost F p R A Y H hr; have h0: heatS F A Y 0≠0:=by rw [heat_zero F p R A Y H hr];simp
       have ha:ContDiffAt ℝ ∞ (loopS F R Y) 0:=(loop_so F p R Y H hp).of_le le_top
       rw [sub_eq_add_neg (Real.log ∘ _),paste_sum (Real.log ∘ _) (-loopS F R Y) (hv.log h0) ha.neg, paste_turn _ ha,waxed F p R A Y H hr]; unfold D; abel
    have hh:= comparison T' T _ _ _ 1 1 (baseP D W) _ (one_mul _) he ht; rw [show MvPolynomial.C.mapMatrix _ = (1:Matrix (Pine G S F) (Pine G S F) (MvPolynomial (wire G c) ℝ)) from by ext i j d; by_cases h:i=j <;> simp [*,Matrix.one_apply]] at hh; exact ⟨_,hh⟩
variable (h:Solved T (flush F u A (novel p R f))) (hz:0<T.saddle.P.det)
include h hz
-- Pass to the actual pin held at all periods. Identifies 1-loop.
lemma rung :
     let S:= out T (flush F u A (novel p R f)); let G':=victory F u p R Y; let H':= thermal F u p R Y A ∘ arm G c 1
     coeff 0 S= -coeff 2 (paste G') ∧ MvPolynomial.homogeneousComponent 3 (coeff 1 S)= -coeff 3 (paste G') ∧ MvPolynomial.homogeneousComponent 4 (coeff 2 S)= -coeff 4 (paste G') ∧ MvPolynomial.homogeneousComponent 2 (coeff 2 S)= -coeff 2 (paste H') := by
   intro S' G' H'
   obtain ⟨y,hY⟩:= pealed F u p R A Y H hr T hG hS hp
   let W:=pending F u p R Y; let L:=wambu F R A Y; let T':= originH T.saddle W
   have hw: ContDiffAt ℝ ∞ W 0:= (pend_lit F u p R Y H).of_le le_top; obtain ⟨hu,hv⟩:= wambu_price F p R A Y H hr hp
   obtain ⟨hT,r,a,b,k⟩:= first_pages hw (freezing F u p R Y H) (key_change T h hw hu hY) hz hv hu
   have hU : out T' (baseP W L)=S':= by have ht:=action_view T' T _ _ hT h _ _ y 1 1 hY; change roam ℝ (fun i=> C _) _=roam ℝ (fun i=> C _) _ at ht; simpa only [virgin] using ht
   rw [←hU]; have hx : W ∘ scalpel (Pine G S F) (wire G c)=G':= ?_
   have hj := strict_thermal F u p R A Y H;
   have ht : ContDiffAt ℝ ∞ H' 0:= by
      have hp:0<(dimR (gateP W) 0).det:= by rw [key_change T h hw hu hY]; exact hz
      have hs: ContDiffAt ℝ ∞ (thermalD W L) 0:= ContDiffAt.add (ContDiffAt.comp (g:=L) (f:=scalpel (Pine G S F) (wire G c)) _ (by rw [map_zero]; exact hv) (scalpel (Pine G S F) (wire G c)).contDiff.contDiffAt) (contDiffAt_const.mul ((paint_a _ (gale_caps W hw)).log hp.ne'))
      exact ContDiffAt.congr_of_eventuallyEq (f:= -(thermalD W L)) hs.neg (hj.mono fun x h=> by rw [Pi.neg_apply,h]; simp [H'])
   unfold T'; rw [b,paste_replace hj,paste_turn H' ht,map_neg]; unfold W at hx; rw [← hx];exact ⟨r,a,k,rfl⟩
   case _=> ext v; rw [Function.comp_apply]; unfold W pending; rw [packed, show firstL _=0 from rfl,map_zero,zero_add];rfl
end YM.FormalBulk08.Hay
