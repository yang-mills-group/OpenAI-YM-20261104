import YM.OPE.Compatible.Pendulum.Natal
/-! Monetary packaging usable for non-root zero-flow compare as well as root. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {I : Type}
   {G:Gauge}{C:Family G}{L:Extraction.Order}(A:Allot C)(hG:G.Simple){φ:Filter I}{s T z r Q:I→ℝ}
    {k:I→ℕ}{d J b:ℕ}
set_option quotPrecheck false
variable (hT:Tendsto T φ atTop)(hk:Tendsto k φ atTop)(hp:Round φ T (fun i=> C.S.a (k i)/s i)) (hβ:Round φ T (fun i=>β C (k i))) (hz:Round φ T (fun i=>z i/Q i))(hr: Round φ T (fun i=>r i/Q i)) (h:∀ᶠ i in φ,0<Q i)
include hp
omit hp
include hz h
lemma purse_self : ∀ᶠ i in φ,0 < z i:=by filter_upwards [hz.pos,h] with i hi hp using pos_of_mul_pos_left (b:=(Q i)⁻¹) (by rwa [← div_eq_mul_inv]) (inv_pos.mpr hp|>.le)
include hT hk hp hβ hG A
lemma weighted (d:ℕ): Round φ T (fun i=>2*owed C (z i) d (k i)*(Q i/s i^d)):=by
    have hs:= purse_self hz h; have hx:= ((owed_cost A hG hT hk hβ hs d).mul (hp.power d hT)).div hz
    apply ((Round.const zero_lt_two hT).mul hx).adjust; filter_upwards [hs] with i hi; have he:=C.S.a_pos (k i); rw [div_pow]; field_simp
omit A hG hk hβ hz
include hr
lemma weighted_stakes (b J:ℕ): Round φ T (fun i=> (stakes C J b/ lantern C.path (r i) d (k i) b)*(Q i/s i^d)):=by
    have he := (hp.power d hT).div hr; let K:= stakes C J b /C.S.a b^d; have h0:0 < K:= div_pos (Real.exp_pos _) (pow_pos (C.S.a_pos _) _)
    apply ((Round.const h0 hT).mul he).adjust; filter_upwards [h] with i hi; unfold K lantern; simp_rw [div_pow]; change _=stakes C J b/(r i*(C.S.a b^_ /C.S.a (k i)^_))* (Q i/_); simp only [div_eq_mul_inv,mul_inv_rev, inv_inv]; ring
omit hr
include A hG hk hβ hz
lemma weighted_rebate (hk':C.ref d ≤ b): Round φ T (fun i=> 2*(stakes C J b/ rebate C (z i) d b (k i)) * (Q i/s i^d)):=by
    have hV:= repol A hG hT hk hβ (purse_self hz h) hk'; have he:= ((hp.power d hT).div hV).div hz
    have hψ:0<2*(stakes C J b):=mul_pos zero_lt_two (Real.exp_pos _); apply ((Round.const hψ hT).mul he).adjust
    filter_upwards [purse_self hz h] with i hi; rw [div_pow]; have hp:=C.S.a_pos (k i); field_simp
end YM.OPE.Arboreal.Pixel
