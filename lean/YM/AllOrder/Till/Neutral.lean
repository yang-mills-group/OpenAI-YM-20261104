import YM.AllOrder.Till.Ovals
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Till
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Matrix
open Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {k w:ℕ} {n : Side}
local notation "T" => RG.Atom G k
open AnalyticBridge VerifiedReset Next.Scheduling
open Floe StateE
/-! Prove exact affine null with compressed curvature. No β until assembly. -/
abbrev nextV (s:ℕ→T)(w:ℕ):= pillar (legible s w) (w:=w)
namespace nextV
variable (s:ℕ→Atom G k)(p:BudgetPoint) (U:Config G n) (o:Site n)(w:ℕ) {t C:ℝ} (h:Quoted s t C)(ht:0<t) (hw:4*k≤ w)
local notation "I"=> Plan k w
local notation "P"=> nextV s w
def soul (w:ℕ)(o:Site n)(U:Config G n):=∑ i:Plan k w,yawn (nextV s w i) o U
include ht h hw
lemma coin(i:I): (P i).Invariant:= Till.turns _ (leg_pays s h.pay ht w) ht i (fun i=> scheme_sym w _ (h.symm i))
lemma brave: Charged P t C:= priceF _ (fun i=>window_cost _ _ hw) (leg_pays s h.pay ht w) ht
lemma plies : soul s w o U=∑' j,(legible s w j).unmasked U o:= (Till.total _ (fun i=>window_cost _ _ hw) (leg_pays s h.pay ht w) ht o U).symm
lemma esprit : p.Regular (court o w) (soul s w o) ∧ p.supBounds o (court o w) (soul s w o) (C*(Wages.startup G k p.power p.order *p.threshold^k*(1+(w:ℝ))^(Wages.grade k p.power p.order))):= by
 obtain ⟨hA,hB⟩:=good_sum p univ (fun (i:I) _=>unit_price (P i) p o (coin s w h ht hw i) (life _ i)); refine ⟨hA,sup_le hB ?_⟩; have hx:0≤ Wages.startup G k p.power p.order:= by unfold Wages.startup; have he:= Wages.slot_ge G p.power p.order 0; positivity
 let f i:=(P i).budget t; let v :ℝ:=Wages.startup G k p.power p.order*p.threshold^k*(1+(w:ℝ))^Wages.grade k p.power p.order; have hζ : 0≤ v:=by unfold v; have hh:= p.threshold_pos; positivity
 calc
  _ ≤ ∑ i:I, f i*v:= Finset.sum_le_sum fun i _=> by
       let A:=Wages.startup G k p.power p.order *p.threshold^k; rw [Wages.scan]; change A*_ *_ ≤ _; have hp:A ≥ 0:= by unfold A; have h:=p.threshold_pos; positivity
       rw [show f i*v=A*f i*((w:ℝ)+1)^Wages.grade k p.power p.order by unfold v A; rw [add_comm 1]; ring]; have hF:0≤A*(f i):=mul_nonneg hp (paid_nonneg ..); gcongr
       · exact Atom.lower_budget _ _ ht
       exact life ..
  _ ≤ _:= by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (budget_sum (brave s w h ht hw) _) hζ
omit ht h hw in
lemma one (hk:0<k): soul s w o 1=0:= Finset.sum_eq_zero fun i _=> loop_root _ hk _
local notation "A₀"=>affinity
omit ht h hw
section two
variable (Sx:ℕ→Atom G 2)(hv:8≤w) (hX:Quoted Sx t C)(u:LinearJet G)
include ht hX hv
private lemma earmark (i:Fin 2→PlaqAxes)(b:Fin 2→G.ColorIndex): ∑ j:Plan 2 w, charge (nextV Sx w j) i b=0:= by
 let V:=legible Sx w; have he (j:ℕ) : charge (V j) i b=charge (Sx j) i b:= by dsimp only [V,legible,Function.comp_apply]; unfold scheme; split <;> rfl
 let hb:Silent (Sx):= hX.mute rfl; have hx:HasSum (fun j=>Extra.Iteration.charge (V j) i b) 0:= by simp_rw [he]; exact (hb i b).1
 have hC (j:Plan 2 w) : charge (nextV Sx w j) i b=∑' k:ℕ, if planned (p:=V) j k then charge (V k) i b else 0:= by
     change (if (fun k=>(j.feet k).plaq)=i then ∑' k, if planned (p:=V) j k then (V k).coeff b else 0 else 0)=_
     split
     next ht=>
        refine tsum_congr fun k=>?_; split; next hh=> change _= ite _ _ _; rw [show (V k).leg=j.feet from hh,if_pos ht]
        next hh=> rfl

     next ht=>
        symm; refine Eq.trans (b:=∑' _k:ℕ,(0:ℝ)) (tsum_congr (fun k=>?_)) tsum_zero; split; next hh=> unfold Extra.Iteration.charge; rw [show (V k).leg=j.feet from hh,if_neg ht]
        next hh => rfl
 simp_rw [hC]; rw [joinS V (fun i=>window_cost _ _ hv) _ hx.summable, hx.tsum_eq]
lemma hushed : ∑ j:Plan 2 w,affinity (nextV Sx w j) u=0:= by
 let g(i:Fin 2→PlaqAxes)(j:Fin 2→G.ColorIndex):=∏ a, (u.positive (i a)) (j a)
 have hz(a:Atom G 2): affinity a u=∑ i:Fin 2→PlaqAxes, ∑ b:Fin 2→G.ColorIndex, charge a i b*g i b:= by
     symm; rw [sum_eq_single (fun i=>(a.leg i).plaq)]; simp only [Extra.Iteration.charge,if_true]; rfl; intro j hj he; refine Finset.sum_eq_zero fun i hi=> ?_; rw [charge,if_neg he.symm,zero_mul]; simp
 simp_rw [hz]; rw [sum_comm]; refine Finset.sum_eq_zero fun i _=>?_ ; rw [sum_comm]; simp_rw [← Finset.sum_mul,earmark w ht Sx hv hX]; simp
end two
variable (hi:2≤k) (hn: Nonwrapping (court o w) o) (hc:4≤n.val) (g:G.Simple)
include h ht hn hc hi g hw p
lemma neutral(i:LinearJet G): logHessian (soul s w o) (i.field o) (i.field o)=0:= by
 let q:=i.field o; let X:= soul s w o; have he:= hessian_limit g (esprit s p o w h ht hw|>.1) (one s o w (by omega)) q;

 have hx:Tendsto (fun t:ℝ=> X (line q t)/t^2) (𝓝[≠] 0) (𝓝 0):= by
    rcases lt_or_eq_of_le hi with hi|hi; · unfold X soul; simp_rw [Finset.sum_div]; simpa only [Finset.sum_const_zero] using (tendsto_finsetSum univ (fun (x:I) _=> more i o hn hc (P x) (life ..) hi))
    subst k; unfold X soul; simp_rw [Finset.sum_div]; have hh:=tendsto_finsetSum univ (fun (x:Plan 2 w) _=> siege i o hn hc (nextV s w x) (life ..)); rw [hushed w ht s hw h i] at hh; exact hh
 have H:=tendsto_nhds_unique he hx; change logHessian (soul s w o) q q=0; linarith only [H]
end nextV
end YM.AllOrder.Till
