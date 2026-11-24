import YM.RGLocalTaylor.Read.Cleared
/-!
# Use of a local Taylor Invoice with the true kinetic, path and scalar prices

Work in the same representation at an arbitrary Spring-inspired step of this
recipe. Powered on the pre-projections and the full logPrice (`orient`), then
supply the estimate after the forced mergers ready to actual normalization.
These statements about `core` (and consequently `sharded`) do *not*
change that any K determinations must use all model and tail inputs at once.

Mark calculus & non-read deltas in other currencies (e.g. motion) must keep
that separation. Proofs adapted from VERIFIED_RESET_STEP/{Projection,...}.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post.Anchor
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens
open AnalyticBridge VerifiedReset Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat Collection Extra.Iteration Song Refrain Geo Quotes
open Residual WilsonStartup Averaging Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open UVNext.CouplingReset Input
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint}
    {X : Listing G n} {v a b : Collection.Source G n} {σ C Λ α Δ u w : ℝ}
open RGLocalTaylor.Read

lemma projection_cap (h : orient p X.reg v.logRead u) : Projects (X.read v) p u:= by
  obtain ⟨f,hf,hH⟩:= h; exact ⟨fun i=>(hH i).1,f,fun i=>(hH i).2,Quotes.segment _ (fun i=>(hH i).2.1) hf⟩

-- linearity including curvature/reset terms.
variable (hG:G.Simple) (hv:v.logRead=a.logRead+b.logRead) (he:orient p X.reg v.logRead u) (hh:orient p X.reg b.logRead w)
include hv he hh
lemma residual_balance : orient p X.reg a.logRead (u+w):= by rw [show a.logRead=v.logRead-b.logRead from eq_sub_of_add_eq hv.symm]; exact orient.subtract he hh

include hG
lemma kinetic : Averaging.delta (X.read v) = Averaging.delta (X.read a)+Averaging.delta (X.read b) := by
  let A:= Averaging.delta (X.read a)
  have ha:= projection_cap (residual_balance hv he hh)
  have hV:= projection_cap he; have hk:= projection_cap hh
  unfold Averaging.delta Averaging.total; rw [← Summable.tsum_add (ha.seriesAt hG ..) (hk.seriesAt hG ..)]; apply tsum_congr; intro i
  unfold censusAt Listing.read; split
  · have h:= projection_sub (X.reg i) (hV.regular i) (ha.regular i) axes01 axes01
    have hb : v.logRead i-a.logRead i=b.logRead i := by rw [hv]; exact add_sub_cancel_left ..
    dsimp only [Listing.read] at *; rw [hb] at h; rw [h]; ring
  exact (zero_add _).symm

omit hG in
lemma vacuum_delta (τ τ' : ℝ) : |vac v τ - vac a τ'|≤ |τ-τ'|+w:= by
  have hk:= residual_balance hv he hh; obtain ⟨he,hH⟩:= orient.flat_tsum hh
  unfold Collection.vac; let Q:ℝ:= sites n; have hQ:0<Q:= sites_pos _
  let c' := ∑' k,b.logRead k 1
  rw [hv,show (∑' i,(a.logRead+b.logRead) i 1)= (∑' i,a.logRead i 1)+c' from Summable.tsum_add (orient.flat_tsum hk).1 he,add_div]
  have hs:|c'/Q|≤ w:=by rw [abs_div,abs_of_pos hQ,div_le_iff₀ hQ,mul_comm]; exact hH
  let u : ℝ:= (∑' i,a.logRead i 1)/ sites n
  change |τ-(u+c'/Q)-(τ'-u)|≤ _
  rw [show τ-(u+c'/Q) - (τ'-u)=τ-τ'-c'/Q by ring]
  exact (abs_sub ..).trans (add_le_add_right hs _)

omit hv he hh hG
variable (R c p X v a b α)
-- only E, using all hard choices separately at the committed density.
abbrev central : ℕ → Config G n → ℝ := (Rack.widen (shelves X R p) (branch X R c p v α)).regular
lemma log_identity (U:ℕ) (b θ:ℝ) : (finish R c p (shelves X R p) (branch X R c p v α) b θ).activities.E U=central R c p X v α U := rfl

variable {p X a b v}
include hv he hh hG
omit hv he hG hh in
private lemma congr_read (h:(v-a).logRead=b.logRead) (i:EKey n) : archive X R c (v-a) 0 Δ i=archive X R c b 0 Δ i:= by unfold archive; simp_rw [h];

lemma core_add : (branch X R c p v α).regular=(branch X R c p a α).regular+(branch X R c p b 0).regular := by
  apply funext; intro i; let A:= Averaging.delta (X.read a); let V:= Averaging.delta (X.read v); let B:= Averaging.delta (X.read b)
  let q:= numbering (EKey n) i
  have hk : V-A=B:= sub_eq_iff_eq_add.mpr ((kinetic hG hv he hh).trans (add_comm A B))
  change archive X R c v α V q=archive X R c a α A q+archive X R c b 0 B q
  rw [add_comm]
  apply sub_eq_iff_eq_add.mp
  calc
    _ = archive X R c (v-a) 0 (V-A) q:= archive_sub (p:=p) (X:=X) (projection_cap he).regular (projection_cap (residual_balance hv he hh)).regular R α _ _ _
    _ = archive X R c (v-a) 0 B q:= by rw [hk]
    _ = _ := congr_read R c (show v.logRead-a.logRead=b.logRead from congr_arg (fun h=> h-a.logRead) hv |>.trans (add_sub_cancel_left ..)) q

lemma central_add : central R c p X v α=central R c p X a α+central R c p X b 0 := by
  funext i; unfold central Rack.widen; dsimp only [Pi.add_apply]; let I:=shelves X R p
  by_cases he': i∈ Set.range (Rack.upE I)
  · obtain ⟨t,rfl⟩:=he'; have h0 (f:ℕ → Config G n→ℝ) := stuffed (Rack.upE I) f t
    rw [show I=shelves X R p from rfl] at h0
    rw [h0, h0, h0]; exact congr_fun (core_add R c α hG hv he hh) t
  have h0 (f:ℕ → Config G n→ℝ) := blank _ f he'
  unfold I at h0; rw [h0,h0,h0,zero_add]
end YM.RGLocalTaylor.Post.Anchor
