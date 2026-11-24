import YM.Integration.WilsonConditionalTaylorBulkContinuity
import YM.Integration.WilsonConditionalTaylorBulkShape
import YM.Integration.WilsonConditionalTaylorRetile

/-! One entire original unmarked Wilson period-to-cover step for a changed
fine field, including its Haar Jacobian, geometric blocking, saddle mean,
connected Gaussian contractions and the true quadratic head. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkPass
open FormalBulk08
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat Mesa Tree Work.F05 Bank
open WilsonConditionalTaylorBulkRows WilsonConditionalTaylorBulkShape WilsonConditionalTaylorBulkInlet
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {j t : ℕ} (P : Flight j t) (L : Lodge P.patch) (W : Pot G)
    (ρ : ChartRatio G) (h : P.patch.Branches K G) (k : ∀ n, (primary P.patch K n).Choices)
    (U : (n : Side)→Pap (wire G n))

/-- The prior prices here apply to the genuine *unblocked* old finite
spatial action, on its own finer torus. No prior price asks for an outgoing
Wilson integral, forest contraction, Haar term, or new scalar counterterm. -/
theorem full (hp : Vivid W) (hr : LocalRatio ρ) (room : 4 ≤ t) (e r : ℕ) (where_ : Fin r)
    (head : ∀ n, coeff 0 (U n)=crunch (kernelP G K.penalty P.wing n)) (shape : ∀ n,Ranks (U n))
    (previous : ∀ a ≤ e, ∀ d, 0 < d → d ≤ e+2 → ∃ w : ℝ, 0 < w ∧
      Kith w (W a d) (fun n=>rancho (U n) a d)) :
    ∃ s : ℝ, 0 < s ∧ Kith s (waken P L W ρ h e r)
      (fun n=>rancho (Reef.landed P ρ h L n (k n) (U (n*P.L))) e r) := by
  cases e with
  | zero =>
    obtain ⟨u,s,C,hs,fee⟩:=head_bill (G:=G) P.land K.penalty K.penalty_pos room r
    have top n:=Reef.landed_cost P ρ h L n (k n) (U (n*P.L)) (head _) hr room
    refine ⟨s,hs,?_⟩
    simp only [waken,rancho,top,head_forms _ K.penalty K.penalty_pos room r where_]
    exact stable hs.le u fee where_
  | succ e =>
    refine WilsonConditionalTaylorBulkContinuity.contraction P L W ρ h k (fun n=>U (n*P.L)) hp hr room e r
      (by have:=where_.isLt;omega) (fun n=>head _) (fun n=>WilsonConditionalTaylorBulkShape.paid P L ρ h n (k n) _ hr room (shape _)) ?_
    intro a ha d hd useful
    obtain ⟨s,pos,bill⟩:=previous a ha d hd useful
    have B:1 ≤ (P.L.val:ℝ):=by exact_mod_cast P.L.property
    have rankBill : Kith s (altitude P.patch W a d) (fun n=>rancho (joust (unitSplit G (primary P.patch K n) 1) (U (n*P.L))) a d) :=by
      simp only [joust_level]
      exact WilsonConditionalTaylorRetile.scaled P.L (τ:=s) (by nlinarith [mul_nonneg (sub_nonneg.mpr B) pos.le]) pos.le bill
    exact sourced P L ρ h k (fun n=>U (n*P.L)) W hr room a d ⟨0,hd⟩ pos rankBill

end YM.Integration.WilsonConditionalTaylorBulkPass
end

