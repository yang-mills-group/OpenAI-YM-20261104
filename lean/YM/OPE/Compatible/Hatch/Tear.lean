import YM.OPE.Compatible.Wells.Zone
/-! # Cost transport into orthogonal cube. Projection preserves Hardy plateau. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
open Aloof
noncomputable def SillV (n:Side)(G:Gauge)(b:ℕ): Bid.Dir G n→L[ℝ] Bid.Dir G n:=ContinuousLinearMap.pi fun i=> if Trim b ((driftB n).symm i) then ContinuousLinearMap.proj i else 0
lemma viewζ (x:D!)(i:Edge (Site n))(b:ℕ): SillV n G b x (arkE i)= if Trim b i then x (arkE i) else 0:=by unfold SillV; rw [ContinuousLinearMap.pi_apply, show (driftB n).symm (arkE i)=i from (driftB n).symm_apply_apply i]; split<;> rfl
lemma saltP (x:D!)(b:ℕ):Roster (SillV n G b x) ≤Roster x:=by
       refine receiveE _ _ (ros x) (fun i=>?_ ); obtain ⟨i,h⟩:= arkSur i; rw[←h,viewζ]; split; exact rentE ..; rw [norm_zero]; exact mul_nonneg (tensile _|>.le) (ros x)
lemma Sill_price (x:D!)(b:ℕ): ‖SillV n G b x‖≤ (1+(b:ℝ))*Roster x:=by
       refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (ros x))).2 (fun i=>?_ ); obtain ⟨t,ht⟩:=arkSur i; rw [← ht,viewζ]; split
       · rename_i hp; exact (rentE x _).trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl _) (Nat.cast_le.mpr hp.1)) (ros x))
       rw [norm_zero]; exact mul_nonneg (by positivity) (ros x)
lemma sillB (x:D!)(b:ℕ): SerT (SillV n G b x) b:= fun i h=>of_not_not fun he=> h (by rw[viewζ,if_neg (show ¬Trim b i from he)])
lemma SillV_id (x:D!)(h:SerT x b): SillV n G b x=x:=by funext i; obtain ⟨t,ht⟩:=arkSur i; rw [← ht,viewζ]; split; rfl; rename_i hi; exact (not_not.mp fun hp=> hi (h t hp)).symm -- proof
lemma Sill_sail (R:Board n (r+1))(x: Chamber G r)(h:r+1 ≤ b): SillV n G b (sailT G R x)=sailT G R x:= SillV_id _ ((sparse_s G R x).raise h)
lemma Sill_pin (R:Board n (r+1))(x:D!)(h:r+1 ≤ b): PinT (r:=r) G (SillV n G b x)=PinT G x:=by
       funext i; rw[PinS G R (SillV _ _ _ _),PinS G R x i,show terr R i=arkE (dig R i) from rfl,viewζ]; let he:= ledgeT (r:=r) R (x:=dig R i) (ported ..); exact if_pos (show Trim b _ from ⟨he.1.trans h,he.2.trans h⟩)
lemma wind (x:D!)(R:Board n b)(p:Finset (Edge Cover))(hp:p⊆bark b):BlurD G p n (SillV n G b x)=BlurD G p n x:=by
       funext i; rw[echoP,echoP,viewζ,if_pos (guardM R _ (hp i.property))]
lemma splitS (x:D!)(i: Site n) (p:Axis) (hi:pdist i < b): SillV n G b x (arkE (i,p))=x (arkE (i,p)):=by rw [viewζ]; exact if_pos ⟨hi.le,(boulder p i).2.trans hi⟩ -- Lattice.Site alias?
lemma tyre (x:D!)(b:ℕ): sillM G n b (SillV n G b x)=sillM G n b x:=by
        funext i; obtain ⟨⟨v,a⟩,h⟩:=arkSur i; by_cases ht:pdist v < b; · rw[←h, reveal _ _ (show pdist (arkE (v,a)).1<b from ht), reveal _ _ (show pdist (arkE (v,a)).1<b from ht),splitS x v a ht]
        rw[←h,fade _ _ (show b ≤ pdist (arkE (v,a)).1 from not_lt.mp ht),fade _ _ (show b ≤ pdist (arkE (v,a)).1 from not_lt.mp ht)]
lemma rAdd (x y:D!):Roster (x+y)≤Roster x+Roster y:=by unfold Roster; rw[map_add]; exact norm_add_le ..
lemma rSub (x y:D!):Roster (x-y)≤Roster x+Roster y:=by unfold Roster; rw[map_sub]; exact norm_sub_le ..
end YM.OPE.Merchant
