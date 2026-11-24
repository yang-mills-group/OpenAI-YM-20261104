import YM.RG05Readout.Planes.Cover
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L

section Algebra
-- projections cut grammar
lemma val_low (j:J)(p : Palette C d): val ((ΠΩ) p) j= if weights j≤ e then val p j else 0:=rfl
lemma span_low (e:ℕ)(p:Palette C d): Address.clear C d e (Address.clear C d e p)=Address.clear C d e p:=by funext k j; change val (Address.clear C d e _) (Sigma.mk k j)= val (Address.clear C d e p) (Sigma.mk k j); rw [val_low, val_low]; split<;>rfl
lemma zero_high (v:Palette C d): ΠΩ ((T) v)=0:=by change ΠΩ (v - ΠΩ v)=_; rw [map_sub,span_low,sub_self]
lemma swell_mark (x:Palette C d): ΠΩ (Ω x) = Ω (ΠΩ x):=by
    funext j a; change val _ (Sigma.mk j a) = val _ ⟨j,a⟩; rw [val_low,amplifies,amplifies,val_low]; split; rfl;rw [mul_zero]
lemma swell_rest (x:Palette C d): (T) (Ω x)= Ω ((T) x):=by change Ω x - ΠΩ (Ω x)= Ω (x- ΠΩ x); rw [map_sub,swell_mark]
lemma atop (x:S) : size ((T) x) ≤ size x:= clear_above e x
lemma size_splits (x:S) : size x ≤ size ((T) x)+size (ΠΩ x):=by let Y: S:= ΠΩ x; exact (size_compare x (ΠΩ x)).trans (by change size Y+size (x-Y) ≤ size (x-Y)+size Y; rw [add_comm])
lemma first_low (x:S):((L).val:ℝ)^(d-e) * size (ΠΩ x)≤ size (ΠΩ (Ω x)):=by
    rw [swell_mark, ← charge_sum]; change _*(∑ i:J,_) ≤ _; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j hj
    rw [val_low]; split
    next he=> exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (a:=(L|>.val:ℝ)) (by exact_mod_cast (C.S.block i).property) (show d-e ≤ d-weights j from Nat.sub_le_sub_left he d)) (norm_nonneg _)).trans_eq (mul_comm ..)
    rw [norm_zero,mul_zero,zero_mul]
lemma overhead (x:S)(_he:e < d) : size ((T) (Ω x)) ≤ ((L).val:ℝ)^(d-(e+1))*size ((T) x):=by
    rw [swell_rest,← charge_sum]; change _≤ _*∑ i:J,_; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j hj
    change ‖val (x-ΠΩ x) j‖* chargeN L j ≤ _*‖val (x-ΠΩ x) j‖; rw [show val (x-ΠΩ x) j =_ from (show val (x-ΠΩ x) j=val x j-val (ΠΩ x) j from rfl),val_low]; split
    next ht=> rw [sub_self,norm_zero,mul_zero,zero_mul]
    next h=> rw [mul_comm]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast (L).property) (by omega)) (norm_nonneg _)
-- BeamLine high zeros. consume only r contour remainder on that corner. This was after projection! so not scaled by extra L^d at input x already in θunits.
lemma leaked {M:Palette C d→ₗ[ℂ]Palette C d}(hp:Contour C i d t s α M)(x:S)(hx:ΠΩ x=0) : size (ΠΩ (M x))≤ α* size x:=by
   obtain ⟨q,hQ,hV⟩:=hp; let z:= Slide (Ω x) q
   have hv: ΠΩ z=0:=by
      unfold z Slide; rw [_root_.map_sum]; apply Finset.sum_eq_zero; intro j hj; rw [_root_.map_smul]; by_cases he:weights j≤ e
      · rw [amplifies,show val x j=0 from ?_,mul_zero,zero_smul]
        have hp:= val_low (e:=e) j x; rw [hx,if_pos he] at hp; exact hp.symm
      have hy: ΠΩ (q j)=0:=by
          funext i k; let a:J:=⟨i,k⟩; change val (ΠΩ (q j)) a=0; rw [val_low]; split
          next hz=> exact hQ.strict j a (Nat.le_trans hz (Nat.le_of_not_ge he)) (by intro H; exact he (H ▸ hz))
          rfl
      rw [hy,smul_zero]
   exact (le_trans (le_of_eq (show size _=size (ΠΩ (M x-z)) from by rw [_root_.map_sub,hv,sub_zero])) ((size_cap ..).trans (hV x)))
end Algebra
end YM.RG05Readout.Planes
