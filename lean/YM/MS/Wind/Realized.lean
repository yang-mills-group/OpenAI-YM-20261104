import YM.MS.Wind.SatGrad
/-!
# Flow Ward: derivative and an all-time mark law

No chosen Gram. Absolute-length sign and ∂ rank yields zero anomaly. Tests polynomial
 in y come from Fees. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Modeled
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{u:ℤ} {k:ℕ}{l:List (Lane4 G)}
variable (x:ℝ)
local notation "X"=> payR F x
local notation "Y"=> payR H x
local notation "ξ" => Ω G
local notation "pb"=> (2:ℂ)⁻¹
local notation "Xx"=> (2:ℂ)
variable (h:PC G p F)
section includeH
include h
lemma JF i: TouchF (F i x):= ((h.owes i).stay x).joint
lemma obstacle {t:ℝ}{b: Bool}(hp:∀ i, Fees b u (H i)): Pieces (Cpu G t) (Mood G t) (Z G) μzone (payR F x t) (payR H x t):= by
   let Q i := (h.owes i).stay x; let W i := (hp i).stay x; exact cert t _ _ (JF x h) (fun i=> (W i).joint) (fun i=> (Q i).perk t) (fun i=> (W i).perk t) (fun i=> (Q i).sym t) (fun i=>(W i).sym t) (fun i=> (Q i).turnt t)
set_option maxHeartbeats 400000 in
lemma unit_field (n:ℕ)(w:List (Lane4 G))(hw:net w=0)(t:ℝ) : HasDerivAt (fun t:ℝ=> mat F x t n w) ((ξ t).lives (X t) (mat F x t) n w) t:= by
   let U := (Ω G t).grow (X t); let V:=(Ω G t); let C0:= pairW V.C
   obtain hv:= (Jpart x t (JF x h) (prior h x t) (fun i=> period0 μzone cour0 (mood_f G) (t:=t) (growT x (JF x h) i)) n); -- hv Q
   obtain ht := (Cpart x t (prior h x t) (prior h x t) n); -- binder order
   have hE : ((Ω G t).lives (X t) (mat F x t)) n w= ((promote V.J U+ promote V.L (X t)+ pb • (pairW V.D (X t) (X t)+ C0 (X t) U+C0 U (X t))) n) w:= (congr_fun (point_mat μzone (obstacle x h (fun i=> h.owes i)) hw) n).symm
   rw [hE]; convert! (hv w).add ((ht w).const_mul pb) using 1; simp only [Pi.add_apply,Pi.smul_apply,C0,smul_eq_mul, U,V]; abel
lemma mark_field (hm:PM φ F H u)(k:ℕ)(t:ℝ) : Zip (fun t=>res F H x t k) ((ξ t).lives (X t) (res F H x t) k + pairW (ξ t).X (mat F x t) (Y t) k) t := by
    intro w; let uh := (ξ t).lives (X t) (Y t); let vf:=(ξ t).grow (X t); have hh i:= ((hm.owes i).stay x).joint;
    obtain hv := Jpart x t hh (priorM h hm x t) (fun i=> period0 μzone cour0 (mood_f G) (t:=t) (livesT x (JF x h) hh i)) k;
    obtain ht := Cpart x t (prior h x t) (priorM h hm x t) k;
    have he : ( (ξ t).lives (X t) (res F H x t) k + pairW (ξ t).X (mat F x t) (Y t) k) w = (( (ξ t).res (X t) uh +promote (ξ t).L (Y t)+pairW (ξ t).D (X t) (Y t)+pairW (ξ t).C vf (Y t)) k) w:= by
       refine congr_fun (congr_fun (point_sole μzone (obstacle x h hm.owes)).symm k) w
    rw [he]; convert! (hv w).add (ht w) using 1; simp only [GridR.res,Pi.add_apply, uh,vf]; abel

-- capacity of residual. Need Rank_at family uniform from owes. prove for linearized elements.
lemma total_slot {b: Bool}(hm:∀ n,Fees b u (H n))(n:ℕ)(c:ℂ):
   let U := fun t:ℝ=>(promote (ξ t).J (Y t)+ c • pairW (ξ t).C (X t) (Y t)) n; TouchF U∧∃ r, Rank U r:= by
    intro U; have ht i:= (hm i).stay x|>.joint; have hv i := (h.owes i).stay x|>.joint; refine ⟨?_,?_⟩; · exact (TouchF.add (TouchF.add (charge_touch (Z G) (flowSmooth G) (ht n)) (lapid_touch (ht n) (mood_f G))) (TouchF.scale c (liveTouch x hv _ (mood_f G) (Xrev G) ht n)))
    choose RH H0 using (fun i:ℕ=> (hm i).pay); choose RF F0 using (fun i:ℕ=> (h.owes i).pay); let S:= Finset.Iic n; let M:= S.sup RF+S.sup RH; have Hq i (he:i≤n) (t:ℝ): Limit (H i x t) M:= (H0 i x t).up (by have hu : RH i≤ S.sup RH:=Finset.le_sup (f:=RH) (Finset.mem_Iic.mpr he); omega)
    have Fq i (he:i≤n) (t:ℝ): Limit (F i x t) M:= (F0 i x t).up (by have hu : RF i≤ S.sup RF:=Finset.le_sup (f:=RF) (Finset.mem_Iic.mpr he); omega)
    refine ⟨2*(M:ℤ),fun t=> Limit.add ( Limit.up (Limit.add ( Modeled.Qmax _ (Hq n n.le_refl t)) ( Limit.up (Modeled.lapQuote (period0 μzone cour0 (mood_f _) (ht n)) (Hq n n.le_refl t)) ?_)) ?_) ?_⟩; · omega
    · omega
    refine Limit.smul _ (Limit.sum (antidiagonal n) fun i hi=> Limit.up (Modeled.guard (Fq i.1 (by obtain he:= Finset.mem_antidiagonal.mp hi; omega) t) (Hq i.2 (by obtain he:= Finset.mem_antidiagonal.mp hi; omega) t) _) ?_); omega
end includeH
end YM.MS.Wind
