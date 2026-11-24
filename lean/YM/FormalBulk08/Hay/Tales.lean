import YM.FormalBulk08.Hay.Scale

/-! Change of variables for input germs at stationary. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f n:Side}{S:StepData c f}(F:Forest S.ratio)
variable (u:S.Choices)(p:Clip)(R:PathData G)(A:ChartRatio G)
variable (Y:Bid.Dir G c→AxisChart G F)(H:Critical F p R Y)
-- input from planned archive

def novel (n: Side): Pap (wire G n):= -afterX (paste (intended p R)) 2 - paste (turnSeries R.loop)
section gadget
variable {I J : Type*} [Fintype I] [Fintype J]
omit [Fintype I] in lemma novel_rope (p:Pap I)(h:coeff 1 p=0): p-C (coeff 0 p)= X^2* afterX p 2:= by
   ext1 i; rw [map_sub,coeff_C,coeff_X_pow_mul']; by_cases hz:2 ≤ i
   · rw [if_pos hz,if_neg (by omega),sub_zero,after_one]; rw [Nat.add_sub_of_le hz]
   rw [if_neg hz]; have hh:i=0 ∨ i=1:=by omega
   rcases hh with a|a <;> subst i <;> simp [*]
omit [Fintype I] [Fintype J] in
lemma reads_lane (p:Pap I)(h:coeff 1 p=0)(a:ℝ)(he:coeff 0 p=MvPolynomial.C a)(f:I→Pap J): roam ℝ f (afterX p 2)=afterX (roam ℝ f p) 2:= by
   have hh:roam ℝ f p= C (MvPolynomial.C a)+X^2 * roam ℝ f (afterX p 2):= by
      have hp:p=C (MvPolynomial.C a)+X^2 * afterX p 2:= by rw [←novel_rope p h,he]; abel
      nth_rw 1 [hp]; simp [roam]
   ext1 i; rw [after_one,hh,map_add,coeff_C,if_neg (by omega),zero_add,coeff_X_pow_mul'];simp
end gadget

abbrev yAxis (x:Rot F G):= graft F (together (secondL x) (summit F Y x))
variable (hG:G.Simple){σ K B:ℝ}(hp:R.Bounds p σ K B)(hS:S.patch.Branches S.kernel G)
include H hG hp
lemma novel_go : dish (motor (summit F Y)) (unmixed (wire G c)) (seat F (novel p R f))= -afterX (paste (fun x=>intended p R (offer G F (summit F Y x)))) 2 - paste (loopS F R Y):= by
   let X:= turnSeries R.loop (m:=f); let W:= summit F Y; let T:=offer G F ∘ W
   have hm : motor (id:Link G c→Link G c)=unmixed (wire G c):= funext fun i=> motor_wires id i
   have ht:=summit_pay F p R Y H; have he:= summit_zero F p R Y H
   rw [←hm,drinking F W id ht contDiffAt_id he rfl]; unfold novel;rw [map_sub,map_neg]
   let f':= intended p R (m:=f); have hu:= strain (m:=f) p R hp
   have hx := point_quiet hG hu 1 (by omega) Nat.one_pos
   have hn : coeff 1 (paste f')=0:= by rw [paste_coeff,hx]; simp [laden]
   have hQ:T 0=0:= by unfold T; rw [Function.comp_apply,show W 0=0 from he,map_zero]
   have hZ:ContDiffAt ℝ ∞ T 0:= ContDiffAt.comp _ (offer G F).contDiff.contDiffAt (ht.of_le le_top)
   rw [reads_lane (paste f') hn _ (paste_first _) (motor T),←paste_steps f' T hu.analytic.contDiffAt hZ hQ,←paste_steps X T (turns_analytic R.loop hp.width hp.two).contDiffAt hZ hQ];rfl
include hS
omit hp hG in
lemma nova_toll : dish (motor (summit F Y)) (unmixed (wire G c)) (roam ℝ (motor (graft F)) (noisePin (G:=G) S u)) = afterX (paste (clack S u ∘ yAxis F Y)) 2:= by
   let X:=summit F Y; have hm:motor (id:Link G c→Link G c)=unmixed (wire G c):= funext fun i=> motor_wires id i
   have he:=summit_zero F p R Y H; have ht:=summit_pay F p R Y H
   let D:= graft F ∘ hitch X (id:Link G c→Link G c); rw [←hm, dessert F X id ht contDiffAt_id he rfl]; change roam ℝ (motor D) _=_
   have hp: hitch X (id:Link G c→Link G c) 0=0:= hitch_zero X id he rfl
   have hu:D 0=0:= by unfold D; rw [Function.comp_apply,hp,graft_origin]
   have hD:ContDiffAt ℝ ∞ D 0:= ContDiffAt.comp _ (hp.symm ▸ (graft_receipt F).of_le le_top) (hitch_smooth _ _ (ht.of_le le_top) contDiffAt_id)
   have hx:= (applause S hS u (G:=G)).2.1
   rw [noisePin,reads_lane _ ?hz _ (paste_first (clack S u)) (motor D), ←paste_steps (clack S u) D (discord S hS u|>.of_le le_top) hD hu]; rfl
   case hz => apply orbit_ext;intro x;rw [trace_paste]; simp [PertExtension.Series.Radial.jet,hx,traceP]
lemma pending_tie : dish (motor (summit F Y)) (unmixed (wire G c)) (roam ℝ (motor (graft F)) (vacuumU u (novel p R f)))= -afterX (paste (pending F u p R Y)) 2 - paste (loopS F R Y):= by
   rw [vacuumU,map_sub,map_sub];change dish _ _ (Reef.seat F (novel p R f))-_=_;rw [show dish (motor _) _ _=_ from novel_go F p R Y H hG hp,nova_toll F u p R Y H hS]
   let f' (x:Rot F G):= intended p R (offer G F (summit F Y x)); let g':= clack S u ∘ yAxis F Y
   have he: pending F u p R Y=ᶠ[𝓝 0] f'+g':=(ferry_light F p R Y H).mono fun x hx=> by
       change mainTerm p R (lifting _ _ _)+noiseTaylor S _ (lifting _ _ _) _=mainTerm p R (input G f _) + clack S u _; rw [←hx]; rfl
   have hp:ContDiffAt ℝ ∞ f' 0:= ContDiffAt.comp (g:=intended p R (m:=f)) (f:=fun x=>offer G F (summit F Y x)) 0 (by rw [summit_zero F p R Y H,map_zero];exact (strain p R hp).analytic.contDiffAt) (ContDiffAt.comp _ (offer G F).contDiff.contDiffAt ((summit_pay F p R Y H).of_le le_top))
   have ht: ContDiffAt ℝ ∞ g' 0:= by
       apply ContDiffAt.congr_of_eventuallyEq (f:=pending F u p R Y-f') ((pend_lit F u p R Y H).of_le le_top |>.sub hp); exact he.mono fun x hx=> by rw [Pi.sub_apply,hx,Pi.add_apply]; abel
   have hs : afterX (paste (pending F u p R Y)) 2=afterX (paste f') 2+afterX (paste g') 2:= by rw [paste_replace he,paste_sum _ _ hp ht];ext1 i;rw [after_one,map_add,map_add,after_one, after_one]
   rw [hs]; abel
-- unused implicit orders note.
end YM.FormalBulk08.Hay
