import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Synchronous
/-!
# The two sweeps are synchronized through the physical Far radius s=r T

Total analytic budget, to be used on the actual hypothesis of the construction. Raw buys are
on the unmarked prediction. Inputs `Mileage`, `Round` required even for calculation of first
M.2 (NOT for second!). Add `Seal` and go to the receding T for full M.3. Release from filters
in the next file. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m h z : ℕ}
variable {V : Arenas G} {B : ℝ→Frames G} {R : ℝ→PowerSeries ℂ}
    {I O : Type*} {K : Set (Points n)} {S : Set (Points m)}
    {W U a b c:ℝ}
    {d : Fin n→ℕ} {e : Fin m→ℕ} (hd : ∀ i,d i≤z) (he : ∀ i,e i≤z) (hh : h ≤ z)
    {D : Route G}
abbrev Probe (O : Type*) (G : Gauge) (h : ℕ) (e : Fin m→ℕ) := Sweep O G (fun _ : Fin 1=> h) e

def probed (Y : Probe O G h e) (D : Route G) (o : O) (r T : ℝ) (y : Points m) (v : Slots G e) : Sec G h →ₗ[ℂ] ℂ :=
  let X := at_far Y D o r T 0 y
  { toFun := fun a => X (fun _=>a) v
    map_add' := fun a b => by
      have ha (c : Sec G h) : (fun (_ : Fin 1) => c) = update (fun (_: Fin 1)=>a) 0 c := funext (Fin.forall_fin_one.mpr (by simp))
      rw [ha (a+b), MultilinearMap.map_update_add, ← ha, ← ha, _root_.add_apply]
    map_smul' := fun c a => by
      have ha (b : Sec G h) : (fun (_ : Fin 1) => b) = update (fun (_: Fin 1)=>a) 0 b := funext (Fin.forall_fin_one.mpr (by simp))
      rw [ha (c • a), MultilinearMap.map_update_smul, ← ha]; rfl }

-- `packet` exact, only Near x; `O` may contain additional origin, viewer parameters.
abbrev Comet (O : Type*) (G : Gauge) (d : Fin n→ℕ) (h : ℕ) := O→ℝ→Points n→Slots G d→Sec G h

/-- Consume G.6's price on the true spatial OPE. Must be applicable uniformly in viewers
and profiles, with power `δ` *independent* even of b. -/
def Seal (F : Sweep O G d e) (F' : Probe O G h e) (packet : Comet O G d h) (D : Route G)
    (U a b W : ℝ) (K : Set (Points n)) (S : Set (Points m)) (δ : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, T ≤ a * g0 G r ^ (-b) →
    ∀ x ∈ K, ∀ y ∈ S, ∀ o, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ‖at_far F D o r T x y u v-probed F' D o r T y v (packet o r x u)‖ ≤
        C* (g0 G r)⁻¹^δ*(r*T+(T⁻¹)^(h+1))

/-- Inputs to first line, only at order p and prepared windows in T. Use
actual calls there (Reader file). -/
structure Prepared (V:Arenas G) (B:ℝ→Frames G) (θ:ℝ→ℝ) (F:Sweep O G d e) (F' : Probe O G h e)
    (hd : ∀ i,d i≤z) (he : ∀ i,e i≤z) (hh : h ≤ z) (D : Route G)
    (W a b : ℝ) (K : Set (Points n)) (S : Set (Points m)) (p : ℕ) : Prop where
  mileage : Mileage G B θ D a b W
  full : Round V θ F hd he p a b W K S
  probe : Round V θ F' (fun _=>hh) he p a b W {0} S

variable (L : Law V R B) (P : _root_.YM.FVA2.O.Canon.Physical V R B)
    (hK : IsCompact K) (hk : K⊆conf n) (hS : IsCompact S) (hs : S⊆Outside m)
    (hw : 1 ≤ W) (hz : clears W K S) (hU : 0 ≤ U)
    {θ : ℝ→ℝ} (sim : G.Simple) (Hθ : Calibrated G θ) (F:Sweep O G d e) (F' : Probe O G h e)
    (p : ℕ) (run : Prepared V B θ F F' hd he hh D W a b K S p)
    {X:Filter I} {x : I→ Points n} {y : I→Points m}
    (hu : ∀ᶠ i in X,x i∈K) (hv : ∀ᶠ i in X, y i∈S) {T r : I→ℝ}
    (hi : Tendsto r X (𝓝[>] 0)) (hT : ∀ᶠ i in X, W ≤ T i)
    (ha : ∀ᶠ i in X, T i ≤ a*(g0 G (r i)) ^ (-b)) (o : I→O)
    {u : I→ Slots G d} {v : I→ Slots G e} (U1 : ∀ᶠ i in X, u i ∈ Balls U G d) (U2 : ∀ᶠ i in X, v i ∈ Balls U G e)
local notation "μ" => (fun i:I=> g0 G (r i))
local notation "η" => (fun i:I=> -Real.log (T i))
local notation "cost" => (fun i:I => T i^(∑ j,e j)*(μ i)^(p+1))
local notation "YY" => (fun i:I=> at_far F D (o i) (r i) (T i) (x i) (y i) (u i) (v i))
local notation "YX" => (fun i:I=> crop p (θ (r i)) (measurement V B hd he (x i) (T i • y i) (η i) (u i) (v i)))
local notation "DD" => (fun i:I=> probed F' D (o i) (r i) (T i) (y i) (v i))
local notation "DX" => (fun i:I=> predicted V B he hh (T i • y i) (η i) (v i) p (θ (r i)))

include hw hs in
lemma central_clear : clears W {(0:Points 1)} S := by
  rintro T hT x rfl' y hy; rw [Set.mem_singleton_iff] at rfl'; rw [rfl', ← squeeze_T T (by linarith [hw])]; exact lives _ (hs hy)

include hU U1 in
lemma basisCost (b : BasisSlots G d) : Fare T X (fun _=>1) (fun i=>coordinates b (u i)) :=
  Fare.cent (U1.mono fun i hi=>coord_price hU _ hi b)

include run Hθ hK hk hS hs hw hz hU sim hu hv hT hi ha L P U1 U2
lemma comparison : Fare T X cost (fun i=> YY i - YX i) ∧ Fare T X cost (fun i=> opCost (DD i-DX i)) := by
  refine ⟨ sweeping L P hK hk hS hs hw hz hd he sim Hθ run.mileage hu hv hi hT ha o F p run.full (basisCost hU U1) (basisCost hU U2), costed (hT.mono fun i h=> hw.trans h) ?_ ⟩
  intro i
  have hc : {(0:Points 1)}⊆conf 1 := singleton_subset_iff.mpr (injective_of_subsingleton _)
  simp_rw [LinearMap.sub_apply,center_read]
  exact sweeping L P isCompact_singleton hc hS hs hw (central_clear hs hw) (fun _=>hh) he sim Hθ run.mileage
    (Eventually.of_forall fun _ => Set.mem_singleton _) hv hi hT ha o F' p run.probe (fun _=> Fare.constant _) (basisCost hU U2)

lemma estimateFirst : ∃ C : ℝ, 0<C ∧ ∃ q:ℕ, ∀ᶠ i in X, ‖YY i-YX i‖ + opCost (DD i - DX i) ≤ C*(cost i)*(1+Real.log (T i))^q := by
  obtain ⟨A,B'⟩:= comparison hd he hh L P hK hk hS hs hw hz hU sim Hθ F F' p run hu hv hi hT ha o U1 U2
  obtain ⟨l,hl⟩:= A; have hY : Fare T X cost (fun i => ‖YY i-YX i‖) := ⟨l, isBigO_norm_left.mpr hl⟩
  have ht := hT.mono fun i h=> hw.trans h; obtain ⟨C,hC,z,H⟩:= Fare.pays ht (ht.and ((pace sim).comp hi|> now) |>.mono fun i h=> show 0 ≤ cost i from mul_nonneg (pow_nonneg (zero_le_one.trans h.1) _) (pow_nonneg h.2.le _)) (Fare.add ht hY B')
  exact ⟨C,hC,z,H.mono fun i h=>le_trans (show _ ≤ |(_ : ℝ)| from (le_abs_self _)) h⟩

lemma estimateCombined (packet : Comet O G d h) (δ : ℕ) (hseal : Seal F F' packet D U a b W K S δ)
    (reach : ℕ) {φ : ℝ} (hb : 0 < b) (hφ : 0 < φ) (hφ' : φ < 1)
    (hp' : reach+b*((↑(∑ j,e j):ℝ)+h+φ)+1 ≤ p+1) (hδ : (reach:ℝ)+δ+1 ≤ b*(1-φ))
    (hc : 0<c) (hm : ∀ᶠ i in X, c * (μ i) ^ (-b) ≤ T i) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ i in X,
      checkPrice (YY i) (YX i) (DD i) (DX i) (packet (o i) (r i) (x i) (u i))
        (purchased V (u i) (x i) h p (θ (r i))) ≤ C * T i ^ (-((h:ℝ)+φ)) * μ i ^ reach := by
  obtain ⟨hr,hg⟩ := comparison hd he hh L P hK hk hS hs hw hz hU sim Hθ F F' p run hu hv hi hT ha o U1 U2
  have ht := (pace sim).comp hi; have HP := now (g:=μ) ht; have T' := hT.mono fun i h=> zero_lt_one.trans_le (hw.trans h)
  have Hθ : ∀ᶠ i in X, |θ (r i)| ≤ 1 ∧ |θ (r i)| ≤ 2*μ i := (hi.eventually (coupling_payment sim Hθ)).mono fun i h=>h.2
  have TT : T=Θ[X] fun i=>μ i ^ (-b) := by
    refine ⟨IsBigO.of_bound a ?_,IsBigO.of_bound c⁻¹ ?_⟩
    · filter_upwards [ha,T',HP] with i h ht hi; simpa only [Real.norm_of_nonneg ht.le,Real.norm_of_nonneg (Real.rpow_nonneg hi.le (-b))] using h
    filter_upwards [hm,T',HP] with i h ht hi; rw [Real.norm_of_nonneg (Real.rpow_nonneg hi.le _),Real.norm_of_nonneg ht.le, ← div_eq_inv_mul]; exact (le_div_iff₀ hc).mpr (by rw [mul_comm]; exact h)
  obtain ⟨M,hM,cost'⟩:= hseal
  have hSale : (fun i=> YY i-DD i (packet (o i) (r i) (x i) (u i)))=O[X] (fun i=> (μ i)⁻¹^δ*(r i*T i+ ((T i)⁻¹)^(h+1))) := by
    refine IsBigO.of_bound M ?_
    have hi' := hi.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))
    filter_upwards [hT,ha,T',HP,hi',hu,hv,U1,U2,hi.eventually cost'] with i h hw ht hi hl x y H K hh
    rw [Real.norm_of_nonneg (by change 0 < r i at hl; positivity)]
    exact (hh _ h hw _ x _ y _ _ H _ K).trans_eq (mul_assoc ..)
  obtain ⟨C,hC,H⟩:= (summary L P ht (r:=r) (fun p=> (length sim p).comp_tendsto hi)
    (t:=θ ∘ r) (Hθ.mono fun i h=>h.1) (Hθ.mono fun i h=>h.2) hb TT hT hw hU hK hk hS hs hz hu hv hd he hh U1 U2 reach p YY DD (fun i=> packet (o i) (r i) (x i) (u i)) hr hg δ hSale hp' hδ).exists_pos
  refine ⟨ C,hC,?_ ⟩; filter_upwards [H.bound,T',HP] with i h hT hi
  rw [Real.norm_of_nonneg (checkPos ..),Real.norm_of_nonneg (by unfold margin; positivity)] at h; exact h.trans_eq (mul_assoc ..).symm
end YM.FVA2.GradedFar259.Comparing
