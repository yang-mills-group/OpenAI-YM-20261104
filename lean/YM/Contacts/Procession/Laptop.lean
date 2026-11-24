import YM.Contacts.Procession.Lilac
import YM.Planned.PRIMARY_INTEGRAL_295.Edens
/-! The polynomial-keeping canonical harmonic filter applies in every period of the analytic step. Can use truths on this representative via Slope & Health. No alterations to Rep.history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Pierian
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch Hinges Lotus Welcome.Theater
open Barrage Barrage.Slope Barrage.Reserve Barrage.Reserve.Oasis Odor Odor.Winding Odor.Winding.Sales Port
open Planned.PrimaryIntegral295 Carrier
variable {G:Gauge}{n k i r l p j:ℕ}{b c d:ℝ}{X ι: Type}
variable (e:Oasis G)(E:∀ n,RackCore e.a e.M n)(x:G.ColorIndex)
-- all statements use the P from Actor, not stamping plot
open Place MultiNext.SignedSource Pattern Shuttle.Tide.Morning
open Place MultiNext.SignedSource Pattern Shuttle.Tide.Morning
variable {F:Field (Fin k) (Node (Dye G))}{L:Side}{x:Dye G}{s η:ℝ≥0}{a d:ℝ}{R:Spine.voyage L}
lemma print_self {F: Field (Fin k) X}(h:Poem F): printRun F=F:=funext fun x=> by
    letI:DecidableEq (Fin k):=fun _ _=>Classical.propDecidable _; unfold printRun; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]; simp_rw [show ∀ p:Equiv.Perm (Fin k),reorder p F x=F x from (fun p=> h p x)]; rw [sum_const,card_univ,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ (a:=(Fintype.card (Equiv.Perm (Fin k)):ℝ)) (by positivity),one_mul] -- arg b
lemma reign {F:Field (Fin n) (Node X)}{p:Equiv.Perm (Node X)}(V:Fin n→Node X→ℝ): say (packing p F) V=say F (fun i=>V i ∘ p):= by
    let P:=Equiv.arrowCongr (Equiv.refl (Fin n)) p; unfold say; rw [← P.tsum_eq]; refine tsum_congr (fun i=>?_); change packing _ _ (p ∘ i)*_= _; rw [pack_io p i p.injective]; rfl -- unused Y synt invalid
lemma toast (j:ℕ)(v:Fin k→ plate G)(h:∀ i, v i∈ rangeLt _ j):∃ b≥(0:ℝ),∀ (s:ℝ≥0)(d:Dye G)(x:Fin k→Node (Dye G)),0<s→ ‖∏ i,sense (G:=G) (v i) (x i)‖ ≤ (b*Shuttle.hail (j*k) s)*fee (terrain s _) (0,d) x := by
    choose a ha using fun i:Fin k=> royalties j (v i) (h i); let T:=∑ i,a i; have hT:0≤T:= sum_nonneg fun i _=>(ha i).1; refine ⟨T^k,pow_nonneg hT _,fun s d x hs=>?_⟩; let g(i:Fin k):= T*blast (x i)^j; rw [norm_prod]; have he:=fame (a:=d) hT hs x (n:=j); rw [Fintype.card_fin] at he; apply le_trans ?_ he; apply prod_le_prod (fun i _=> norm_nonneg _) (fun i _=>?_); let u:=x i; let z:=(verdict (E:=G.Color) (v i)) u.1 (axisEquiv.symm u.2.1); apply (PiLp.norm_apply_le z _).trans; let Y:=ha i|>.2 u.1 (axisEquiv.symm u.2.1); apply Y.trans; exact mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>(ha i).1) (mem_univ _)) (by unfold Carrier.liftCost; positivity)
lemma clashes (h:0<s)(ht:(η:ℝ)/(L.val:ℝ) ≤ s)(he:0<η)(hF: Rest (terrain s _) (0,x) F b)(hr:R.strip η c)(hc:0≤c) (v:Fin k→plate G) (hv:∀ i,v i∈rangeLt _ j):
    Summable (fun u:(Fin k→Node (Dye G))×(Fin k→Node (Dye G))=> (F u.1) *∏ i:Fin k, seen R (verdict (E:=G.Color) (v i)) (u.1 i) (u.2 i)) := by
    let H:= Hinges.placed (influx ht) hF (u:=((0:Cover),x)) (fun _:Fin k=> ledgers (Origin.bleed_strip (G:=G) hr hc) hc); obtain ⟨C,hC,hQ⟩:= toast j v hv; let g:=C*Shuttle.hail (j*k) (η:ℝ); have hg:0≤g:= (by unfold g Shuttle.hail; positivity); let Z:= install (Origin.bleed G R);
    refine Summable.of_norm ((budget_scale hg H).2.1.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=>?_)); unfold seen; rw [prod_mul_distrib,←mul_assoc,norm_mul]; change ‖F i.1*∏ j,Z (i.1 j) (i.2 j)‖ * ‖∏ j,sense (G:=G) (v j) (i.2 j)‖ ≤ g*(‖F i.1*∏ j,Z (i.1 j) (i.2 j)‖*Shuttle.fee _ _ _); rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hQ _ x i.2 he) (norm_nonneg _)
set_option maxHeartbeats 590000 in
lemma stride (h:Whole R)(ht:0<s)(hF:Rest (terrain s _) (0,x) F b)(hq:Poem F)(v P:Fin k→ plate G)(hv:∀ i,v i∈ rangeLt _ j)(hp:∀ i (x:Node (Dye G)), HasSum (seen R (verdict (E:=G.Color) (v i)) x) (sense (G:=G) (P i) x)) :
    say (lifts (Origin.bleed G R) F) (fun i=>sense (G:=G) (v i))= say F (fun i=>sense (G:=G) (P i)):= by
    obtain ⟨σ,C,hσ,hC⟩:=h; lift σ to ℝ≥0 using hσ.le; let t:=min σ s; let A:=max C 0; have he:0<t:= lt_min hσ ht; have hl:(1:ℝ) ≤ L.val:= (by exact_mod_cast (show 1 ≤ L.val from L.property)); have hr:R.strip t A:= strip_mono hC (NNReal.coe_le_coe.mpr (min_le_left ..)) (le_max_left ..); let Z:= install (Origin.bleed G R); have hw:= clashes ht ((div_le_self (NNReal.coe_nonneg t) hl).trans (NNReal.coe_le_coe.mpr (min_le_right σ s))) he hF hr (le_max_right C _) v hv;
    unfold say lifts hoist; rw [print_self (allAt_poem (install (Origin.bleed G R)) hq)]; let I:=Fin k → Node (Dye G); let K(u w:I):=F u*∏ i:Fin k, seen R (verdict (E:=G.Color) (v i)) (u i) (w i)
    have h : Summable (fun p:I×I=> K p.1 p.2):=hw; have hx(w:I): allAt (fun _:Fin k=> Z) F w*(∏ i,sense (G:=G) (v i) (w i))=∑' u,K u w:= by
       rw [allAt,← tsum_mul_right]; apply tsum_congr; intro u; unfold K; simp_rw [seen,prod_mul_distrib]; exact mul_assoc .. -- show shape
    have hh(u:I): ∏ i:Fin k,sense (G:=G) (P i) (u i)=∑' w:I,∏ i:Fin k, seen R (verdict (E:=G.Color) (v i)) (u i) (w i):= by simp_rw [← (show ∀ i:Fin k,_ from (fun i=>(hp i (u i)).tsum_eq))]; exact (Cost.tsum_pi (f:=fun i:Fin k=>seen R (verdict (E:=G.Color) (v i)) (u i)) (fun i=>(hp i _).summable.norm)).2.symm
    simp_rw [show ∀ w:I,allAt (fun _:Fin k=> install (Origin.bleed G R)) F w* _ = _ from hx,hh,← tsum_mul_left]; exact h.tsum_comm
end YM.Contacts.Procession.Pierian
