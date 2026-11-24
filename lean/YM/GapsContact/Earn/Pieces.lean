import YM.GapsContact.Earn.Bondage
/-!
# Rectangular probes and all derivatives for clock interpolation

Graph read *without* extra hypotheses on the unselected frame's real part: evaluate
both real and imaginary on a fixed billing basis. Moves internal layout along S.
Power-log pays at any fixed derivative order (selected later, from wanted valuation estimates,
without varying with i). Stability estimates use differentiating true hierarchy only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open Set Function Filter MeasureTheory Analysis Spec Table Extraction Lattice RG Wilson
open Frontier6 Frontier6.Tale Frontier6.Road Ascent Power Trace Trace.Terrace Trace.Pilot
open OPE OPE.Log MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {C: Family G} {f:Extraction.Order} {S:Table C.book} (F:Final C f S)
variable {I J V:Type}[Fintype I][DecidableEq I][Fintype J]{hG:G.Simple}{A:EveryPhase.Almanac F}
universe u
variable (H:Roll.{u} F hG A)
variable {n d:ℕ}

-- 1. all fields Trek basis directions. log cost finite constants d', grammar cap preserved
local notation "E'"=> F.sector.derivatives
local notation "P'"=> F.room.kernel

def stampCoin (g:ℝ)(v:S.Tag):ℝ:= cost F v.1 g v.2
lemma stampCoin_nn (g:ℝ)(v:S.Tag): 0≤ stampCoin F g v:= Ascent.cost_pos ..
include H
lemma upward_price (d:ℕ)(p:Axis) : ∃ B:ℝ,1≤B ∧ ∀ g∈ Ioc (0:ℝ) 1,∀v:S.Tag,v.1=d→ g*stampCoin F g (Ward.rise E' p v) ≤ B*stampCoin F g v:=by
   obtain ⟨B,hB,h⟩:= cash_derivative F H d p; refine ⟨B,hB,fun g hg v hv=>?_⟩; rcases v with ⟨b,v⟩; change b=d at hv; subst b; exact h g hg v
lemma trek_stamp (d:ℕ)(a:Axis)(k:ℕ):∃ B:ℝ,1≤B ∧ ∀ g∈Ioc (0:ℝ) 1,∀ v:S.Tag,v.1=d → g^k*stampCoin F g (trek E' a v k) ≤ B*stampCoin F g v :=by
   induction k with
   | zero=> refine ⟨1,le_rfl,fun g hg v hv=>?_⟩; rw [pow_zero]; exact le_rfl
   | succ k ih=>
      obtain ⟨B,hB,hC⟩:= ih; obtain ⟨C',hc,hQ⟩:= upward_price F H (d+k) a
      refine ⟨B*C',one_le_mul_of_one_le_of_one_le hB hc,fun g hg v hv=>?_⟩; specialize hC g hg v hv; have ht:= hQ g hg _ ((trek_h (E') v a k).trans (by rw [hv])); rw[pow_succ,mul_assoc]; change _*(g*stampCoin F _ (Ward.rise _ _ _)) ≤ _
      refine (mul_le_mul_of_nonneg_left ht (pow_nonneg hg.1.le k)).trans ?_; rw [mul_comm B C',mul_assoc C',mul_left_comm]; exact mul_le_mul_of_nonneg_left hC (zero_le_one.trans hc)
lemma route_pay (d:I→ℕ)(p:I × Axis)(k:ℕ): ∃ B:ℝ,1 ≤ B∧ ∀ g∈ Ioc (0:ℝ) 1,∀ v:I→ S.Tag,(∀ i,(v i).1=d i)→ g^k*billSlots F g (route F v p k) ≤ B*billSlots F g v :=by
   obtain ⟨B,hB,hV⟩:= trek_stamp F H (d p.1) p.2 k; let z:= p.1
   refine ⟨B,hB,fun g hg v hv=>?_⟩; let P(i:I→ S.Tag):= ∏ j∈Finset.univ.erase z, stampCoin F g (i j); have hh(y:I→ S.Tag): billSlots F g y= stampCoin F g (y z)* P y:=(Finset.mul_prod_erase _ (fun i:I=>stampCoin F g (y i)) (Finset.mem_univ z)).symm
   let v':=route F v p k; have ht:P v'= P v:= Finset.prod_congr rfl fun i hi=> congr_arg _ (Frontier6.Road.route_same F v p k i (Finset.ne_of_mem_erase hi))
   change g^k*billSlots F g v'≤_; rw [hh,hh,show v' z=trek (E') p.2 (v z) k from update_self .., ht,← mul_assoc, ← mul_assoc]; exact mul_le_mul_of_nonneg_right (hV g hg _ (hv _)) (Finset.prod_nonneg (fun _ _=> stampCoin_nn ..))

-- derivatives on exterior columns, using exact same F
variable {a t s:ℝ}{p:I×Axis}{x:I→ E4} {y:J→ E4} {o:E4}
omit H
variable (v:I→ S.Tag)(w:J→ S.Tag)
abbrev trailWord (x:I→ E4) (a:ℝ)(p:I×Axis)(k:ℕ) (s:ℝ) : Spelling S:= assembly S (wag x a p s) (route F v p k)
-- apply Sum.elim for ext helpers -- keep route visible application
lemma route_degree (d:I→ℕ)(hp:∀ i,(v i).1=d i)(j:I) : (route F v p n j).1= update d p.1 (d p.1+n) j:=by
   by_cases he:j=p.1; · subst j; unfold Road.route; rw [update_self,update_self,trek_h,hp]
   rw [Frontier6.Road.route_same F v p n j he,update_of_ne he]; exact hp j
omit [Fintype I] [Fintype J] in
lemma route_mates (n:ℕ)(p:I×Axis) : route F (beside v w) (Sum.inl p.1,p.2) n=beside (route F v p n) w:=by
   unfold Road.route beside; ext1 i; rcases i with i|i
   · dsimp only [Sum.elim_inl]; by_cases h:i=p.1; subst i; simp only [update_self]; rw [update_of_ne (Sum.inl_injective.ne h),update_of_ne h]; rfl
   rw [update_of_ne (by simp)];rfl
lemma route_joint (h:Injective (beside (wag x a p s) y))(z:StateIndex F)(k:ℕ): HasDerivAt (fun s=>a^k • peal F z (trailWord F v x a p k s*assembly S y w)) (a^(k+1) • peal F z (trailWord F v x a p (k+1) s * assembly S y w)) s:=by
    let p':(I⊕J)×Axis:=(Sum.inl p.1,p.2); have hx(s:ℝ):wag (beside x y) a p' s=beside (wag x a p s) y:=by
        unfold wag beside; ext1 i; rcases i with i|i
        · dsimp only [p',Sum.elim_inl]; by_cases h:i=p.1; subst i; simp only [update_self]; rw [update_of_ne (Sum.inl_injective.ne h),update_of_ne h]; rfl
        rw [update_of_ne (by unfold p';simp)]; rfl
    have hh:= starter F (beside x y) (beside v w) p' k a z s ((hx s).symm ▸ h)
    simp_rw [hx,(show ∀ n, route F (beside v w) p' n=beside (route F v p n) w from (fun n=> route_mates F v w n p)),beside, Tale.concatenates] at hh; exact hh

lemma joint_deriv {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{f:ℝ→X}{x:X}{t:ℝ} (B:X→ₗ[ℝ] Module.Dual ℝ X)(h:Injective B)(hv:∀ y:X,HasDerivAt (fun r=>B (f r) y) (B x y) t): HasDerivAt f x t:=by
   let T:= Module.finBasis ℝ X; let F':X→ₗ[ℝ] Fin (Module.finrank ℝ X)→ℝ:= LinearMap.pi fun i=> B.flip (T i)
   have ht:Injective F':=by intro x y hx; apply h; exact T.ext fun i=> congr_fun hx i
   obtain ⟨g,hg⟩:= LinearMap.exists_leftInverse_of_injective F' (LinearMap.ker_eq_bot.mpr ht)
   let G:= g.toContinuousLinearMap; have hx(x:X):G (F' x)=x:= LinearMap.congr_fun hg x
   have he := G.hasFDerivAt.comp_hasDerivAt t (show HasDerivAt (F' ∘ f) (F' x) t from hasDerivAt_pi.mpr fun u=> hv (T u))
   rw [hx, show G ∘ F' ∘ f=f from funext fun i=> hx (f i)] at he; exact he -- comp associations

include H
lemma graph_deriv {o:E4} (t:ℝ)(ht:0<t)(hx:Injective (beside (wag x a p s) (fun _ : Unit=> dial t o)))(d k:ℕ) : HasDerivAt (fun s=> a^k • lookup F d o t (trailWord F v x a p k s)) (a^(k+1) • lookup F d o t (trailWord F v x a p (k+1) s)) s :=by
   have hg:= all_good F H t ht d; let B:= Power.bond (F.room.kernel) d t; letI : FiniteDimensional ℝ (S.Field d):= Module.Finite.trans ℂ _
   refine joint_deriv B (bankable (P') ht hg).1 fun y=>?_
   let V(_ : Unit):= (⟨d,flipField F d y⟩:S.Tag); have hh:= route_joint F v V hx none k
   have hy : ∀ (k:ℕ)(s:ℝ), B (a^k • lookup F d o t (trailWord F v x a p k s)) y = (a^k • peal F none (trailWord F v x a p k s * assembly S (fun _ : Unit=> dial t o) V)).re := by
       intro k s; rw [map_smul, LinearMap.smul_apply]; unfold B; rw [graphCore F ht hg,snapshot_read]; unfold assembly; rw [Fintype.prod_unique]; exact (Complex.reLm.map_smul (a^k) _).symm
   simp_rw [hy]; exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hh

lemma walk_deriv {o:E4} (t:ℝ)(ht:0<t) (s':StateIndex F)(hx:Injective (beside (wag x a p s) (fun _ : Unit=> dial t o)))(he:Injective (beside (wag x a p s) y))(d k:ℕ) :
    let f (k:ℕ)(s:ℝ) := let X := trailWord F v x a p k s; a^k • peal F s' ((X-letter S o ⟨d,lookup F d o t X⟩)*assembly S y w)
    HasDerivAt (f k) (f (k+1) s) s :=by
    intro f; have h:= route_joint F v w he s' k; have ht':=graph_deriv F H v t ht hx d k
    let T:= readingMap F o d (assembly S y w) s'; let B:=T.toContinuousLinearMap.restrictScalars ℝ; let X(k:ℕ)(s:ℝ):= a^k • lookup F d o t (trailWord F v x a p k s)
    have he(k s):f k s= a^k • peal F s' (trailWord F v x a p k s*assembly S y w)- B (X k s) := by
       unfold f X; dsimp only; rw [sub_mul,map_sub,smul_sub,map_smul]; simp only [peal, ← Tale.reads F]; rfl
    have hh : HasDerivAt (B ∘ X k) (B (X (k+1) s)) s:=B.hasFDerivAt.comp_hasDerivAt s ht'; rw [he]; exact (h.sub hh).congr_of_eventuallyEq (Eventually.of_forall fun _=> (he ..)) -- orientation
end YM.GapsContact.Seams
