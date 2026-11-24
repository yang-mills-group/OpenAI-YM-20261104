import YM.FormalOPE.RG10.Routes.Debits

/-!
# Two massive bundles, one formal joining step

Price coefficient of binary non-hom error of the full normalized transmission, ordinary on both
separate inputs. Bound controlled ONLY by rank and matched root ℓ1 polynomial moments
geometric type, the pinned vacuum post-square-log vertex price, and same-measure covariance.
These power moments don't assume analyticity/comparison with real side. Units via `Tape` chosen
for ALL at this event. All operations one scale, bounds costed in common `C` with finite powers;
also true at all finite volume periodic tori when hypotheses on those periodic inputs are met.
Not by itself a claim of uniform-in-cutoff approximation, nor a continuum-profile bound at this
endpoint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route.Binary
open Marker Extra.Trajectories FlatFeed Word Polar PowerSeries Finset Joins Joins.Gauss Function
open MvPolynomial (aeval totalDegree)
open Primitives.GCC Grove
open Multi (parts shards)
open Multi.Vacuum.Gauss (Row)
open scoped Topology BigOperators Classical
variable {I J B K X : Type} [Fintype J] [Fintype K] [DecidableEq K]
variable (q : I → Row J) (P Q V : Channel (I⊕B))
variable {T : Tape X} (p : I ⊕ B → X)
local notation "T₀" => Polar.budget bill K
local notation "δ" => posted P Q V
local notation "m" => Fintype.card (Target K)
local notation "r" => Fintype.card K

variable (A E O : Lens T) {L : ℝ} (hY : 0 ≤ L) (hL : A.Spaced E L) (ha : O.m ≤ A.m) (he : O.m ≤ E.m)
    {C : ℝ} (d n : ℕ) (c : Wide K C d)
    [DecidableEq I] [Fintype I] (S D : ℝ) (hS:0≤S) (hD:0≤D)
    (hp:slim P (Fintype.card K) d) (hq:slim Q (Fintype.card K) d) (hv:slim V (Fintype.card K) d)
    (uP:∀ i≤Fintype.card K,worth (A.m ∘ p) (n+n) (coeff i P) ≤ S)
    (uQ:∀ i≤Fintype.card K,worth (E.m ∘ p) (n+n) (coeff i Q) ≤ D)
    (uV:vacuum V p C (Fintype.card K) (n+n) T)
    (u:schur p q T (n+n) C)

-- exponent budget collected in one monomial cap. `d` includes the given rank constraints, `m`
-- depends only on polar size, cost absorbed at that arity.

def peak (d v : ℕ) := (1+4*d)*v+1

def burn (d v : ℕ) := 5+4*v+peak d v
local notation "η" => O.m ∘ p ∘ Sum.inr
variable {k : Finset K} {s : (Multi.parts (Polar.budget bill K)).Mode}
    {a b : Target K} (hm : s∈ shards (Polar.budget bill K) (pay bothMarks k))

include c uP uQ uV hp hq hv u hS hD hY hL ha he
private lemma priced (he':a∈s.val) (ht:b∈s.val) (hx : cuts a false) (hr : cuts b true)
    (hn : b≠a) : tip L n * worth η n (track q s δ) ≤ C^burn d m*S*D := by
  let W (i:Target K) : ℝ := if i=b then C*D else C*C
  have h' : 1 ≤ C := enough C d c; have h0 : 0≤C := zero_le_one.trans h'; have hx' : (d:ℝ) ≤ C:= le_trans (by linarith) c.over
  have hW i : 0≤W i:=by unfold W; split<;> positivity
  have hd i (hi:i∈s.val\{a}) (h:i≠b) : ∀ x,pins p T (n+n) (δ i) x ≤ W i := by
    intro x
    rw [posted,selectGen, mark_vac (fun hq => h (unique_cut (mem_sdiff.mp hi).1 ht hq hr))
      (fun hp => (mem_sdiff.mp hi).2 (mem_singleton.mpr (unique_cut (mem_sdiff.mp hi).1 he' hp hx))), if_pos rfl,
      pins_scale,Complex.norm_natCast]; unfold W; rw [if_neg h]
    apply le_trans (mul_le_mul_of_nonneg_left (uV _ (card_le_univ _) _) (by positivity)) (mul_le_mul_of_nonneg_right (ticket_cost C d c i) h0)
  have hb : worth (E.m ∘ p) (n+n) (δ b) ≤ W b:= by
    rw [posted,selectGen,mark_far hr (fun h => hn (unique_cut ht he' h hx))];
    simp only [marker_ne_quiet,ite_false,Census.fire_inj,Bool.true_eq_false,ite_true,worth_smul,Complex.norm_natCast,W]
    exact le_trans (mul_le_mul_of_nonneg_left (uQ _ (card_le_univ _)) (by positivity)) (mul_le_mul_of_nonneg_right (ticket_cost C d c b) hD)
  have ho : worth (A.m ∘ p) (n+n) (δ a) ≤ C*S:= by
    rw [posted,selectGen,mark_near hx (fun h => hn (unique_cut ht he' hr h))];
    simp only [marker_ne_quiet,ite_false,ite_true,worth_smul,Complex.norm_natCast]
    exact le_trans (mul_le_mul_of_nonneg_left (uP _ (card_le_univ _)) (by positivity)) (mul_le_mul_of_nonneg_right (ticket_cost C d c a) hS)
  have hh:= billed p q δ A E O C n d u (fun i _ => ink P Q V d i hp hq hv) W hd hb h' he' ht hn (fun i _ => hW i) s rfl hY hL ha he -- inspect
  let U:= s.val \ {a}
  have hu : b∈U:= mem_sdiff.mpr ⟨ht,fun h=>hn (mem_singleton.mp h)⟩
  have hw : (∏ i∈U,(d*C)*W i) ≤ C^3*D*C^(4*m) := by
    rw [← mul_prod_erase _ _ hu, show W b=C*D from if_pos rfl]; apply mul_le_mul (le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' h0) (show 0≤C*D by positivity)) (le_of_eq (by ring))) _ (prod_nonneg (fun i _ => mul_nonneg (by positivity) (hW i))) (by positivity)
    refine le_trans (b:=∏ _∈U.erase b,C^4) (prod_le_prod (fun i _ => mul_nonneg (by positivity) (hW i)) (fun i hi=> ?_)) ?_
    · unfold W; rw [if_neg (ne_of_mem_erase hi)]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' h0) (by positivity)).trans (le_of_eq (by ring))
    rw [prod_const, pow_mul]; exact pow_le_pow_right₀ (one_le_pow₀ h') (card_le_univ _)
  have hu' : 0 ≤ ∏ i∈U,(d*C)*W i := prod_nonneg (fun i _ => mul_nonneg (by positivity) (hW i))
  apply hh.trans
  have hA : ((Grove.options s.val {a}).card:ℝ) ≤ C := (Nat.cast_le.mpr (card_le_univ _)).trans c.trees
  have H0 : ((Grove.options s.val {a}).card:ℝ)*(worth (A.m ∘ p) (n+n) (δ a)*∏ i∈U,(d*C)*W i) ≤ C*(C*S*(C^3*D*C^(4*m))) := mul_le_mul hA (mul_le_mul ho hw hu' (by positivity)) (mul_nonneg (worth_nonneg _ (fun i => A.sign (p i)) _ _) hu') h0
  apply (mul_le_mul H0 (rent_admissible C d c (t:=s.val.card) (card_le_univ _) (card_pos.mpr ⟨a,he'⟩)) (rent_sign ..) (by positivity)).trans
  unfold burn peak; exact le_of_eq (by simp only [pow_add]; ring)

include hm in
private lemma shardBudget : tip L n * worth η n (track q s δ) ≤ C^burn d m*S*D := by
  -- ports actually included by the shard; it may include a *same* word with both, in which case
  -- by formal prescription the node is zero.
  obtain ⟨a,ha',hx⟩:= cutting k hm false; obtain ⟨b,hb,hv'⟩:= cutting k hm true
  by_cases h : b=a
  · subst b
    have hy : δ a=0 := by
      rw [posted,selectGen,mark_both hv' hx]; simp
    have h : streets s δ=∅ := Fintype.piFinset_eq_empty.mpr ⟨⟨a,ha'⟩,by rw [hy]; rfl⟩
    rw [track,h,sum_empty, worth_empty,mul_zero]; have : 0≤C:=zero_le_one.trans (enough C d c)
    positivity
  exact priced q P Q V p A E O hY hL ha he d n c S D hS hD hp hq hv uP uQ uV u ha' hb hx hv' h

def burnAll (d v : ℕ) := 1+burn d v
variable (k) (hz : PowerSeries.coeff 0 V=0)
include hz

/-- Order-by-order. `n` indexes polynomial position moment requests; supply twice it in the
stated covariance and interaction and preceding marked costs. Run at width `d` per fixed arity.
The number of finest sites and the gauge dimension excluded from combin power. It's still
conditional on the actual post-square-completion presented coefficients obeying these moments.
-/
theorem summer : tip L n * worth η n (PowerSeries.coeff k.card (disagreement q P Q V)) ≤ C^burnAll d m*S*D := by
  let W : ℝ := C^burn d m*S*D
  let G:= shards T₀ (pay bothMarks k)
  have h0 : 0 ≤ C:= zero_le_one.trans (enough C d c); have hW : 0 ≤ W := by unfold W; positivity
  have h : tip L n * worth η n ((k.card.factorial:ℂ) • PowerSeries.coeff k.card (disagreement q P Q V)) ≤ ∑ _i∈G,W := by
    rw [resolution q P Q V hz k]; apply (mul_le_mul_of_nonneg_left (worth_sum _ (fun i => O.sign (p (.inr i))) n _ _) (tip_pos hY n).le).trans
    rw [Finset.mul_sum]; exact sum_le_sum fun _ hi => shardBudget q P Q V p A E O hY hL ha he d n c S D hS hD hp hq hv uP uQ uV u hi
  rw [worth_smul,Complex.norm_natCast,sum_const,nsmul_eq_mul] at h
  have he' : (G.card:ℝ) ≤ C := (Nat.cast_le.mpr (card_le_univ _)).trans c.mix
  apply le_trans _ (le_trans (mul_le_mul_of_nonneg_right he' hW) (le_of_eq (show C*W=C^burnAll d m*S*D from by
    unfold burnAll W; rw [pow_add,pow_one]; ring)))
  exact le_trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (worth_nonneg _ (fun i => O.sign (p (.inr i))) _ _) (Nat.one_le_cast.mpr <| Nat.factorial_pos _)) (tip_pos hY n).le) h
end YM.FormalOPE.RG10.Route.Binary
