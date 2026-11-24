import YM.RG01Estimate.Aperture
import YM.RG01Estimate.Pruned
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Marlin.Foam
/-!
 # Stellar plate. Same listing on the real output before alias changes.

   Operates on regular log short *difference* quantities on ONE extended
   listing (can include negative candidates from the prescribed step).
   Requires per-label prices BEFORE making those combinations, on each
   real mask. Orbit and future stars operations are actual transformations;
   we don't claim arbitrary equivalences to a canonical polynomial model.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Abacus
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Meadow Marlin Trio
open Geo Footprint Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge}{c : Side} {A: Listing G c} (B:BudgetPoint){t w:ℝ}
   {X F H : Collection.Source G c}
lemma charted (h : Collection.Local A B F t w): Meadow.Budget B A.reg F.logRead t:=
   let ⟨i,hf,hu⟩:= h.cheap; ⟨i,hu,fun j=>⟨h.smooth j,hf j⟩⟩
variable (F) (P : ℕ→ Config G c→ℝ)

def revise : Collection.Source G c:= ⟨P,F.hardRead⟩
-- +p reserves
lemma pay_gap {κ : Type} {p : κ→RegularAddress c} {x y : κ→ Config G c→ℝ} (h : Meadow.Budget B p x t)
    (hp : Meadow.Budget B p y w) : Meadow.Budget B p (x-y) (t+w) := by
   obtain ⟨f,h,hQ⟩:=h; obtain ⟨g,h',hv⟩:=hp; refine ⟨f+g,fun i=>?_,fun i=> ⟨VerifiedReset.reg_sub (hQ _).1 (hv _|>.1), VerifiedReset.sup_sub (hQ _).1 (hv _).1 (hQ _).2 (hv _).2⟩⟩
   have hh:=budget_plus (h i) (h' i)
   simpa only [Pi.add_apply,add_mul,ite_add_zero] using hh
lemma pay_zero {κ : Type} (p:κ→RegularAddress c) : Meadow.Budget (G:=G) B p 0 0:= by
   refine ⟨0,?_ ,fun _=> ⟨VerifiedReset.reg_const _,?_⟩ ⟩
   · intro x; simp [SumBudget]
   exact VerifiedReset.sup_larger (VerifiedReset.sup_le (VerifiedReset.sup_const 0) (abs_zero.trans_le le_rfl)) (by rfl)
lemma pay_bundle {κ : Type} {p : κ→RegularAddress c} {x y : κ→ Config G c→ℝ} (h : Meadow.Budget B p x t)
    (hp : Meadow.Budget B p y w) : Meadow.Budget B p (x+y) (t+w) := by
   have hh:=pay_gap B (pay_zero (G:=G) B p) hp; rw [zero_sub,zero_add] at hh; simpa only [sub_neg_eq_add] using pay_gap B h hh

variable {F P} (V: Config G c)
lemma adds_pow (he: Meadow.Budget B A.reg F.logRead t) (h : Meadow.Budget B A.reg P w) :
    (A.read (revise F (F.logRead+P))).additive B V=(A.read F).additive B V+(A.read (revise F P)).additive B V:= by
   have h':= Marlin.stashes B A F V he; have hp:=Marlin.stashes B A (revise F P) V (show Meadow.Budget B A.reg (revise F P).logRead w from h)
   have hu i:(A.read (revise F (F.logRead+P))).regularOccurrence B i V=(A.read F).regularOccurrence B i V+(A.read (revise F P)).regularOccurrence B i V:= by
        by_cases he:Healthy B.threshold (A.reg i).support V
        · simp [Activities.regularOccurrence,Listing.read,he,revise,masked_eq]
        simp [Activities.regularOccurrence,Listing.read,he,revise,masked_ne]
   unfold Activities.additive; simp_rw [hu]; exact h'.tsum_add hp
lemma raw_eq_of_empty (A:Listing G c)(F:Collection.Source G c)(h:flags B.threshold V=∅) : (A.read F).additive B V=Boulevard.throng F.logRead V:= by
    apply tsum_congr; intro i; exact masked_eq _ _ _ _ (by unfold Healthy; rw [h]; exact Finset.disjoint_empty_right ..)

structure Rack (A : Listing G c) (r:ℕ) (U:ℕ→ Config G c →ℝ) where
   atW : Finset ℕ
   seat : ℕ→Site c→ℝ
   bound : ∀ i∉ atW,U i=0
   sums (i) : i∈ atW → ∑ x:Site c,seat i x=1
   paid (i) : i∈ atW→ ∀ u,0≤ seat i u
   priced (i) : i∈ atW→∀ x,seat i x≠0 → (A.reg i).support ⊆ neighbors r x
variable {r:ℕ} {U:ℕ→ Config G c →ℝ} (p: Rack A r U)
def Rack.polygon : Trio.Offer G c:= fun i=> ∑ j∈ p.atW,p.seat j i • U j
def Rack.maskedEntry (x:Site c) (V:Config G c):= ∑ j∈ p.atW, p.seat j x * masked B.threshold (A.reg j).support (U j) V
lemma Rack.routes (F:Collection.Source G c) : (A.read (revise F U)).additive B V=∑ i : Site c,p.maskedEntry B i V:= by
   let W i:= (A.read (revise F U)).regularOccurrence B i V
   have ht i (h:i∉ p.atW) : W i=0:= by change masked _ _ (U i) _=0; rw [p.bound _ h]; simp [masked]
   unfold Activities.additive; rw [tsum_eq_sum ht]; simp_rw [maskedEntry]; rw [sum_comm]; refine sum_congr rfl ?_; intro i hi; rw [← sum_mul, p.sums _ hi,one_mul]; rfl -- sums order
lemma Rack.chip_healthy (i:Site c)(h: Healthy B.threshold (neighbors r i) V): p.maskedEntry B i V=p.polygon i V:= by
   unfold maskedEntry polygon; rw [Finset.sum_apply]; refine sum_congr rfl fun j hj=>?_
   by_cases hh:p.seat j i=0; · rw [hh]; simp
   exact congr_arg (p.seat j i * ·) (masked_eq _ _ _ _ (h.mono_left (p.priced _ hj _ hh)))

lemma Rack.throng (h: flags B.threshold V=∅) : Boulevard.throng U V= Trio.froth p.polygon V:= by
   let F:Collection.Source G c:= ⟨0,0⟩; have hp:=p.routes B V F
   rw [raw_eq_of_empty B V A (revise F U) h] at hp
   exact hp.trans (sum_congr rfl fun i _=> p.chip_healthy _ _ _ (by unfold Healthy; rw [h]; simp))

lemma Rack.plating (h: Meadow.Budget B A.reg U t) (i:Site c): B.Regular (neighbors r i) (p.polygon i):= by
   obtain ⟨_,_,hM⟩:=h; unfold polygon; apply Meadow.regularA; intro j hj
   by_cases hh:p.seat j i=0; · rw [hh,zero_smul]; exact CouplingShape.reg_const _
   exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hM _).1 (p.priced _ hj _ hh))

-- Loose hit-cost before flags. Needed to pay on bad V even if post-Δ log is tiny.
lemma Rack.reserveW (h: Meadow.Budget B A.reg U t)(u:Site c): ‖p.maskedEntry B u V‖ ≤ (ballCost r:ℝ)*t:= by
   obtain ⟨a,hX,ha⟩:=h; let f (i : ℕ):= masked B.threshold (A.reg i).support (U i) V
   let s:=neighbors r u; let E i x:= if (A.reg i).site=x then a i * Real.exp (preExponent B * coverNumber B.B (A.reg i).support) else 0
   unfold maskedEntry; apply le_trans (norm_sum_le ..)
   calc
     _ ≤ ∑ i∈ p.atW, ∑ x∈s,E i x:= by
         apply sum_le_sum; intro i hi; have hp : 0≤∑ x∈s,E i x:=sum_nonneg fun x _=> (hX x).1 i
         change ‖p.seat i u*f i‖ ≤ _; by_cases ht:p.seat i u=0; · rw [ht,zero_mul,norm_zero]; exact hp
         have he:= p.priced i hi u ht; let W:=p.seat i
         have hW : p.seat i u≤1:= (Finset.single_le_sum (fun j _=> p.paid i hi j) (Finset.mem_univ u)).trans_eq (p.sums i hi)
         rw [norm_mul, Real.norm_of_nonneg (p.paid i hi u)]; apply (mul_le_of_le_one_left (norm_nonneg (f i)) hW).trans; apply (CouplingShape.mask_cost (ha i).2 V).trans
         apply (le_mul_of_one_le_right (ha i|>.2.1) (Real.one_le_exp (show 0≤preExponent B * coverNumber B.B (A.reg i).support from mul_nonneg (Song.headline B).exponent_pos.le (Nat.cast_nonneg _)))).trans
         unfold E; rw [sum_ite_eq,if_pos (he (A.reg i).anchor)]
     _ ≤ (ballCost r:ℝ)*t:= by
         rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hX x) p.atW))
         rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) (Cost.nonneg (hX u))
lemma Rack.grain (h: Meadow.Budget B A.reg U t)(u:Site c)(hv: flags B.threshold V=∅): ‖p.polygon u V‖ ≤ (ballCost r:ℝ)*t:= by
   rw [← p.chip_healthy B V u (by unfold Healthy; rw [hv]; simp)]; exact p.reserveW B V h u

end YM.RG01Estimate.Abacus
