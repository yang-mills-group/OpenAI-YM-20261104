import YM.GradedFar.Polar
/-!
# G.5 & G.8 bridge with a polylog price

At any Near layout of given clearance. Uses fixed true basis and Reader.
The price that will turn the shadow estimate into the one on the actual ordinary packet;
no log convergence on nested shapes from the independent Match used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log MeasureTheory
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Orbits.measO Orbits.borelO Orbits.hμ YM.Work.A15.compact_ortho
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}(F:Final C fo S)
    {I:Type} [Fintype I] (d:I→ℕ) (h j:ℕ)
variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {M δ:ℝ} (hm:0≤M)(hd:0<δ)
local notation "H" => S.Hierarchy
local notation "Spend" => Sold (𝓝[>](0:ℝ))
local notation "OE" => Exterior C.book
local notation "v₀" => (sole : S.Field h → Unit → S.Field h)
variable (u:Labels S d)

lemma fixed {α Z : Type*} {φ:Filter α} {B:α→Z→Prop} {T W : α→Z→ℝ}
    {𝕜 E E': Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E][NormedAddCommGroup E']
    [NormedSpace 𝕜 E][NormedSpace 𝕜 E'] (Q:E→L[𝕜]E'){f:α→Z→E}
    (Hf:Sold φ B T W f) : Sold φ B T W (fun a z=> Q (f a z)) := Hf.transfer (norm_nonneg _)
  (Eventually.of_forall fun _ _ _=> Q.le_opNorm _)

-- an estimate from comparisons at every fixed rotated exterior needed by this Reader
include hm hd in
lemma rotation_sum {f:Launch I→ S.Field h}
    (Ht:∀ e:Exterior C.book, Spend (SmallSpin M δ) TagCost (wage d h) (fun _ (i:Spins I)=> bridgeError F d h u f e i)) :
    Spend (SmallSpin M δ) TagCost (wage d h) (fun _ (i:Spins I)=> spinning Q.port F.sector.turns j i.2.x i.2.center i.1 u -
      spinning Q.port F.sector.turns j (sole i.2.center) i.2.center i.1 (d:=fun _:Unit=>h) (v₀ (f i.2))) := by
  let price (a:Mode F.sector.derivatives) (e:OE) (i:Spins I) : S.Field j := ((Q.port.sheet a) e * bridgeError F d h u f e i) • F.sector.turns.act j i.1 (Q.port.loaded a j)
  let T (p:ℝ) (i:Spins I):= ∑ a∈bands F.sector.derivatives j,∑ e∈(Q.port.sheet a).support, price a e i
  have he : Spend (SmallSpin M δ) TagCost (wage d h) T := by
    apply Sold.sum (F':=fun a (_:ℝ) (i:Spins I)=>∑e∈(Q.port.sheet a).support,price a e i) (wage_ok d h _)
    intro a _; apply Sold.sum (F':=fun e (_:ℝ) (i:Spins I)=>price a e i) (wage_ok d h _); intro e _
    obtain ⟨c,hc⟩:= isCompact_univ.exists_bound_of_continuousOn (Q.law.spin j (Q.port.loaded a j)).continuousOn
    have hn:c ≥ 0 := (norm_nonneg _).trans (hc 1 (Set.mem_univ _))
    apply (Ht e).transfer (show 0 ≤ ‖(Q.port.sheet a) e‖*c by positivity)
    refine Eventually.of_forall fun r i hi=> ?_
    unfold price; rw [norm_smul,norm_mul]; simpa only [mul_assoc, mul_comm c] using
      mul_le_mul_of_nonneg_left (hc i.1 (Set.mem_univ _)) (show 0 ≤ ‖(Q.port.sheet a) e‖*‖bridgeError F d h u f e i‖ by positivity)
  refine he.price ((occupied (I:=I) F Q.port hm hd j).mono ?_); intro r hr i hi; apply le_of_eq
  rw [discrepancy_spin Q.port Q.law Q.continuum F.phase.transport.motion _ _ (hr i.2 hi)]
  simp only [T, price, bridgeError, Finset.sum_smul]

lemma integral_full {K : Type}[Fintype K]{h:K→ℕ}(v:Labels S h){z:Launch K}(he:orbitMargin Q.port j z.x z.center):
    Integrable (fun k=>spinning Q.port F.sector.turns j z.x z.center k v) haar:=by
  refine Integrable.congr (integrable_finsetSum (bands F.sector.derivatives j) (μ:=haar) (f:=fun i=> bears F.sector.turns Q.port i j z.x z.center v)
    (fun i hi =>integrable_bears Q.port Q.law Q.continuum j z.x z.center i v (he i hi))) ?_
  exact Eventually.of_forall (fun k=> (scatter Q.port Q.continuum j z.x z.center v k).symm)
include hm hd in
lemma fundIntegral {f:Launch I→ S.Field h}
    (Ht:∀ e:Exterior C.book, Spend (SmallSpin M δ) TagCost (wage d h) (fun _ (i:Spins I)=> bridgeError F d h u f e i)) :
    Spend (Tiny M δ) TagCost (wage d h) (fun _ (i:Launch I)=> averageV Q.port F.sector.turns j i.x i.center u -
      averageV Q.port F.sector.turns j (sole i.center) i.center (d:=fun _:Unit=>h) (v₀ (f i))) := by
  obtain ⟨k,b,hb,hQ⟩:= rotation_sum F d h j Q hm hd u Ht; refine ⟨k,b,hb,?_⟩
  filter_upwards [occupied (I:=I) F Q.port hm hd j,hQ] with r hmarg hr i hi
  specialize hmarg i hi
  have h0 : orbitMargin Q.port j (sole i.center) i.center := by
    convert (translateMargin j (sole 0) 0 i.center).mpr (centerMargin Q.port j) <;> try simp [sole]
  rw [averageV,if_pos hmarg,averageV,if_pos h0, ← integral_sub
    (integral_full F j Q (z:=i) u hmarg) (integral_full F j Q (h:=fun _:Unit=>h) (z:=⟨sole i.center,i.center⟩) _ h0)]
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using norm_integral_le_of_norm_le_const
    (Eventually.of_forall fun g:Ortho=> show ‖spinning Q.port F.sector.turns j i.x i.center g u - spinning Q.port F.sector.turns j (d:=fun _:Unit=>h)
      (sole i.center) i.center g (v₀ (f i))‖ ≤ b*TagCost r i^k*wage d h r i from hr (g,i) hi :
        ∀ᵐ g ∂haar, _)

variable (bank:LogTrace F Q.port)
local notation "Ω" => replaced F d h u Q
include bank hm hd
set_option maxHeartbeats 600000 in
lemma originBridge : Spend (Tiny M δ) TagCost (wage d h) (fun _ (i:Launch I)=>
    checkReal Q.port Q.law Q.continuum j i.x i.center u - checkReal Q.port Q.law Q.continuum j
        (sole i.center) i.center (d:=fun _:Unit=>h) (v₀ (Ω i))) := by
  let g i:=S.conj F.room.kernel.spin h (Ω i)
  have A := fundIntegral F d h j Q hm hd u (boughtAt F d h Q bank hm hd u)
  have B := fundIntegral F d h j Q hm hd (f:=g) (bar F.room.kernel.spin u) (boughtColor F d h Q bank hm hd u)
  let L := (conjugateR F.room.kernel.spin j).toContinuousLinearMap
  let C := ((2:ℝ)⁻¹ • ContinuousLinearMap.id ℝ (S.Field j))
  apply (fixed C (Sold.add (wage_ok d h _) A (fixed L B))).congr; intro _ i
  rw [checkValue,checkValue,map_sub, (show bar F.room.kernel.spin (d:=fun _:Unit=>h) (sole (Ω i))= sole (g i) from rfl)]
  change (2⁻¹:ℝ) • (_ : S.Field j) = _; rw [← smul_sub]; apply congr_arg; abel_nf; rfl
lemma bridge_poses : Spend (Tiny M δ) TagCost (wage d h) (fun _ (i:Launch I)=>
    Q.fresh j i.x i.center u - Q.cutTest j h (Ω i)) := by
  apply (fixed (Q.knife j).toContinuousLinearMap (originBridge F d h j Q hm hd u bank)).congr
  intro _ i; let w:Labels S (fun _:Unit=>h):=v₀ (Ω i)
  have hg : checkReal Q.port Q.law Q.continuum j (sole i.center) i.center w = checkReal Q.port Q.law Q.continuum j (sole 0) 0 w := by
    apply Eq.trans ?_ (checkReal_transfer j Q.law Q.continuum _ _ _ i.center)
    rw [zero_add,(show (fun j:Unit=>sole (0:E4) j+i.center)=sole i.center from funext (fun _=>zero_add _))]
  rw [map_sub]; change _ - Q.knife j (checkReal Q.port Q.law Q.continuum j (sole i.center) i.center w)=_
  rw [hg]; rfl
lemma packet_pose : Spend (Tiny M δ) TagCost (wage d h) (fun _ (i:Launch I)=>
    Q.packet h i.x u i.center - Ω i) := by
  let f (j:Fin (h+1)):=(F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)).toContinuousLinearMap
  have he j:= fixed (f j) (bridge_poses F d h (j.val) Q hm hd u bank)
  refine (Sold.sum (x:=Finset.univ) (wage_ok d h _) (fun j _=>he j)).congr ?_
  intro _ i
  have hh:=Q.reconstruct h h le_rfl (Ω i); rw [F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts _] at hh
  simp only [map_sub,Finset.sum_sub_distrib]; exact congrArg (Q.packet h i.x u i.center - ·) hh

lemma fresh_price_good (u:Labels S d): Spend (Tiny M δ) TagCost (fun r (_:Launch I)=>r^j/r^(∑i,d i)) (fun _ (i:Launch I)=>
    Q.fresh j i.x i.center u) := by
  let f i:= shadowOld Q.port j (Launch.x i) (Launch.center i) u
  let w(r:ℝ)(_:Launch I):=r^j/r^(∑i,d i)
  have hw: Safe (𝓝[>]0) (Tiny M δ) TagCost w:= compact_pay d _ j
  have hs : Spend (Tiny M δ) TagCost w (fun _ i=> Q.cutTest j j (f i)):=by
    let y a i:= (Q.port.ope a (Launch.x i) (names u) i.center) • Q.cutTest j j (Q.port.loaded a j)
    have he a (ha:a∈ bands F.sector.derivatives j) : Spend (Tiny M δ) TagCost w (fun _ i=> y a i) := by
      have hz: a.fst≤j := (full_bands ..).mp ha
      rcases lt_or_eq_of_le hz with hj|he
      · apply Sold.zero.congr; intro _ i; unfold y; rw [Q.port.cost a ha,Q.cut_rise ..,Q.kills_lower j _ hj _,smul_zero]
      obtain ⟨k,h⟩:= bank.terms _ (names u) δ M hd hm a
      let c : ℝ := ‖Q.cutTest j j (Q.port.loaded a j)‖
      refine ⟨k,c,norm_nonneg _, h.mono ?_⟩; intro r hr z ht
      unfold y; rw [norm_smul]; have h:=(hr z.x z.center ht).2; rw [he] at h
      exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (show (badge r)^k*(r^j/r^(∑i,d i))*c=c*TagCost r z^k*w r z by
        unfold w TagCost; ring)
    apply (Sold.sum hw he).congr; intro _ i; dsimp only [f,shadowOld,OPE.shadow,y]; simp only [map_sum,map_smul]
  have ha := (bridge_poses F d j j Q hm hd u bank).more (hw.mono fun r hr z hz=> zero_le_one.trans (hr z hz).1)
    (show ∀ᶠ r:ℝ in 𝓝[>]0,∀ (z:Launch I),Tiny M δ r z → wage d j r z≤ w r z from by
      filter_upwards [self_mem_nhdsWithin, (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r (hr:0<r) hr' _ _
      unfold wage w; exact div_le_div_of_nonneg_right (pow_le_pow_of_le_one hr.le hr' (show j ≤ j+1 by omega)) (by positivity))
  exact (ha.add hw hs).congr (fun _ z=> sub_add_cancel ..)
end YM.Integration.GradedFar.Fork
