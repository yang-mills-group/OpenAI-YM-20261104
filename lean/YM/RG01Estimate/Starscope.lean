import YM.RG01Estimate.Nodules
import YM.RG01Estimate.Brig
/-!
 # Budget before the affine final. Requires Racks for EACH auxiliary and same
   kernel/germ/forge. Coverage support remains EXACT beyond k. Left derivatives
   paid to p.n. No support reserve borrowed from candidate P.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Promise
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Animals PhysicalNext.Repeat.Fare Sienna Conditioning Token Office Courtyard RealTaylor
open Laplace Laplace.Stellar Series Boulevard Blaze.Frond Exterior Abacus Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Geo Footprint
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}
section generic
-- choose a ticket along evaluated stellar shelves
variable {c:Side}{A:Listing G c}{U:ℕ→ Config G c→ℝ}{y γ η C K :ℝ} {G:Gauge}

end generic
section shape
open Marlin
variable {c:Side} {w r:ℕ} (B:BudgetPoint) (t:ℝ) {y β v η : ℝ} (z:ℕ)
    {Y:Stars→Side} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (P: ∀ i:Stars,Offer G (Y i)) (x:Site c)
    (q:Stars→ℝ) (hp : 0 < β) (hz:w+4 ≤ z)(hy:1<y)
    (h : ∀ i j, B.Regular Finset.univ (P i j))
    (he:∀ (x:Site c) (V: Config G c),Healthy B.threshold (neighbors z x) V→ ∀ i, ∃ (u:Site (Y i)→G.El) (p:Positions (Uniform.Primary (Y i) G)), actual (gStep β • p)= gauge u (Slide.shape (pad Q i) x V)∧ ‖p‖+1<y)
    (hV:∀ i (p:Positions (Uniform.Primary (Y i) G)), flags B.threshold (actual (gStep β • p))=∅→ ‖p‖+1<y→∀ l:List (Directions G (Y i)), l.length≤ B.order →(∀ j∈l,‖j‖≤B.threshold) → ‖leftDerivs (Boulevard.stillA (Trio.froth (P i))) l (actual (gStep β • p))‖ ≤ q i)

local notation "θ" => Trio.ornament Q P
local notation "g" => gStep β
include hp he hV h hz hy
lemma reserve_lo (hh : ∀ i : Site c, (coverNumber B.B (neighbors z i):ℝ) ≤ η):
     Meadow.Budget B (c:=c) (Marlin.leap z) (θ) ((Trio.oroW B z q)*Real.exp (preExponent B*η)):= by
   have hm i: flags B.threshold (actual (gStep β • (0:Positions (Uniform.Primary (Y i) G))))=∅:= by simp only [smul_zero,actual,map_zero,link_one]; exact smoky (Promise.f_one B)
   have hk:0<g:=(Fare.gS β hp).1
   have hq i:0≤ q i:=(norm_nonneg _).trans (hV i 0 (hm i) (by simp; exact hy) [] (Nat.zero_le _) (by simp))
   let A:= Trio.oroW B z q
   have hT x:B.supBounds x (neighbors z x) (θ (x:Site c)) A:= by
     apply Trio.kinds B Q z P h hq hz 0 (g*(y-1)) x
     · intro V hV i; obtain ⟨u,x',hx,ht⟩:= he x V hV i; refine ⟨u,g • x',hx,?_⟩; rw [norm_smul, Real.norm_of_nonneg hk.le,mul_zero, add_zero]; exact mul_lt_mul_of_pos_left (by linarith) hk
     intro i p hK hη
     let c:=g⁻¹ • p; rw [show p=g • c from (smul_inv_smul₀ hk.ne' p).symm]; apply hV _ _ (by unfold c; rw [smul_inv_smul₀ hk.ne']; exact hK)
     unfold c; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hk).le]; have h':g⁻¹*‖p‖< y-1:=(inv_mul_lt_iff₀ hk).mpr (by simpa only [mul_zero,add_zero] using hη); linarith
   have hf : 0≤ A:= (hT (0:Site c)).1
   refine ⟨fun _=> A,fun i=> ?_,fun i=> ⟨?_,hT i⟩⟩
   · apply budget_finite
     · intro i; split; exact mul_nonneg hf (Real.exp_pos _).le; rfl
     rw [Finset.sum_eq_single i]; rw [if_pos (show (leap z i).site=i from rfl)]
     · exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (hh i) (Song.headline B|>.exponent_pos.le))) hf
     · intro j hj he; exact if_neg he
     simp
   rw [Trio.orchard]; apply Meadow.regularA _; intro j hj; apply CouplingShape.reg_scale
   apply Slide.regular; swap
   · intro i'; exact (neighbors_mem ..).2 ((Slide.village ..).trans (by have hh:= j.isLt; omega)) -- edit names
   apply CouplingShape.reg_sub _ (CouplingShape.reg_const _)
   rw [show froth (P j)=∑ i,P j i from funext fun i=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun i _=> h _ _
end shape
end YM.RG01Estimate.Promise
