import YM.FormalBulk08.Kemp.Icy

/-! Marked raft (pointwise). `Youth` rank/parity with input slots l,
closed under nil scalar unit marks too. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I V J: Type*} {m l t:ℕ}

def Yield (k e r : ℕ):= r ≤ k+e
-- parity optionally propagated separately (lower triangular). Need filters that combine
-- upper slot (actual) and max for products; keep simple in primary matrix estimates.
def Young (A:OrbitV V) (k : ℕ) := ∀ e r,A e r≠0 → Yield k e r
lemma youth_egg {A:OrbitV V}{S:OrbitV V}(q:V→V→ℝ)(hA:Young A l)(h:Fiery S)(i e r):
    dipper q (swim q S) A i e r≠0 → Yield l e r ∧ r+2*i≤l+3*e:=by
   induction i using Nat.strong_induction_on generalizing e r with
   | _ i ih=>
     cases i with
     | zero=> simp only [dipper_first]; intro hv; have hx:= hA _ _ hv; unfold Yield at *; omega
     | succ i=>
       simp_rw [dipper_succ];contrapose!;intro hv
       have he:dipper q (swim q S) A i e (r+1+1)=0:=by by_contra hx;have hh:=ih i (by omega) _ _ hx; unfold Yield at *; omega
       rw [he, stare_nil,zero_add];
       suffices h: brawl q (swim q S) (dipper q (swim q S) A) i e r=0 by rw [h,smul_zero,smul_zero]
       apply brawl_vigil; intro a ha b hb w hw; by_contra! hu; have H:=thermal q h _ _ _ hu.1; simp_rw [Finset.mem_antidiagonal] at ha hb hw; have hh:=ih b.2 (by omega) _ _ hu.2;unfold Yield at *;omega
lemma through_dip (q:V→V→ℝ)(A B : Waves V)(R S: OrbitV V)(h:∀ i,∀ b≤m,A i b=B i b)(he:∀ b≤m,R b=S b)(n:ℕ):∀ b≤m,dipper q A R n b=dipper q B S n b:= by
   induction n using Nat.strong_induction_on with
   | _ n ih=> intro b hb; cases n with
              | zero=> rw [dipper_first,dipper_first]; exact he b hb
              | succ n=>funext i; rw [dipper_succ,dipper_succ,ih n (by omega) b hb,bonded_match hb (fun i _=>h i) (fun r hr=> ih r (by omega))]
lemma dye_dip (f: I≃V)(q:I→I→ℝ)(Q:V→V→ℝ)(h:∀ i j,Q (f i) (f j)=q i j)(A : Waves V)(B:OrbitV V)(S:Waves I)(T: OrbitV I)(ha:∀ i n v,S i n v=jetty f (A i n v))(he:∀ n v,T n v=jetty f (B n v))(s e r): jetty f (dipper Q A B s e r)= dipper q S T s e r:= by
   induction s using Nat.strong_induction_on generalizing e r with
   | _ s ih=>
      cases s with
      | zero=> rw [dipper_first,dipper_first,he]
      | succ s=> rw [dipper_succ,dipper_succ]; change ((s+1:ℕ):ℝ)⁻¹ • (jetty f (stare Q (dipper Q A B s e (r+1+1))) + (2:ℝ) • jetty f (brawl Q A (dipper Q A B) s e r))= _;rw [dyes_stare f q Q h, ih s (by omega)]
                 apply congr_arg; apply congr_arg;apply congr_arg
                 unfold brawl reach; rw [jet_sums];apply Finset.sum_congr rfl; intro a _; rw [jet_sums];apply Finset.sum_congr rfl; intro b hb; rw [jet_sums]; refine Finset.sum_congr rfl fun i _=>?_; rw [Finset.mem_antidiagonal] at hb
                 rw [visor_eq,visor_eq,jet_length,jet_sand,dyes_bond f q Q h, ih b.2 (by omega),ha]
-- last cutoff uses upper HB L even if Young l
lemma peat_late [Fintype V] (q:V→V→ℝ)(f Z:Pap V)(hf:coeff 0 f=0)(s:∀ i j,q i j=q j i)
    (h:Fiery (rancho f))(hz:Young (rancho Z) l)(e r B : ℕ)(hB:l+3*e≤B): rancho (late (flare q f Z)) e r=∑ n∈Finset.range (B+1), dipper q (swim q (rancho f)) (rancho Z) n e r:= by
    rw [rancho,marbled_late,posting_dipper q f Z hf s,posting_swim q f hf]; refine tsum_eq_sum fun i hi=>?_ ; by_contra hh;have he:=youth_egg q hz h i e r hh;simp only [Finset.mem_range,not_lt] at hi; omega
lemma extraction_mark [Fintype V] [Fintype I] [DecidableEq V] (H:Hull V I)(p S:Pap (V⊕I))(hp:Solved H p)(he:Fiery (rancho (cobalt H p)))(hv:Young (rancho (lever H S)) l)(e r U:ℕ)(hh:l+3*e≤U): rancho (flag H p S) e r=∑ n∈ Finset.range (U+1), jetty Sum.inr (dipper (aqua H.saddle) (swim (aqua H.saddle) (rancho (cobalt H p))) (rancho (lever H S)) n e r):= by
    rw [tag_sky _ _ _ hp];
    let F:= late (flare (aqua H.saddle) (cobalt H p) (lever H S))
    rw [rancho,coeff_map];change marble r (aftEval V I (coeff _ F))=_
    rw [target_port,show marble r (coeff e F)= rancho F e r from rfl]; unfold F; rw [peat_late (aqua H.saddle) _ _ (cobalt_base H p) (aqua_symm _) he hv e r U hh]; funext v;simp [jetty,Finset.sum_apply]
end YM.FormalBulk08.Kemp
