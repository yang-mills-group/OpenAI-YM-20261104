import YM.GradedFar.MultiCrop
/-!
# Application to the other type of expression (line 1691)

The price of omitting high total-degree terms in a product with **individually** cropped K
fields is also only logarithmic (before evaluation-power factor), despite the heterogeneous
caps and moving Far profiles. Use for comparing with actual field conversion operators in the
first inequality of (M.2).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (A : Arenas G) (F : ℝ → Frames G) (η : ℝ)
    (hd : Through l d) (he : Through l e)
    (x : Points n) (y : Points m)
    (u : Inputs G d) (v : Inputs G e) (p q : ℕ) (z : ℝ)

def bothCrop (p : ℕ) (z : ℝ) (f : ℕ → Both G d e) := ∑ k ∈ Finset.range (p+1), (z:ℂ)^k • f k
lemma bothCrop_apply (f : ℕ → Both G d e) :
    bothCrop p z f u v = crop p z (PowerSeries.mk (fun k => f k u v)) := by
  simp_rw [crop_eq, bothCrop, sum_apply, smul_apply, smul_eq_mul, coeff_mk]

/-- Application uses it with received point rows (mixed caps, at the scaled Far positions).
This is the constant-array unconverted comparison on certain funded inputs. -/
def constantCrop := bothCrop p z (rawCoeff A hd he (forest x (squeeze η y)))
def insertedCrop := bothCrop p z (withFar A (conversion F η) hd he (forest x (squeeze η y)))
lemma insertedCrop_apply : insertedCrop A F η hd he x y p z u v = crop p z (fullSeries A F η hd he x y u v) :=
  bothCrop_apply ..

def cropK (F : ℝ → Frames G) (η : ℝ) (q : ℕ) (z : ℝ) (d : ℕ) :=
    ∑ k ∈ Finset.range (q+1), (z:ℂ)^k • coeff k (conversion F η d)
def cropArguments (F : ℝ → Frames G) (η : ℝ) (q : ℕ) (z : ℝ) (v : Inputs G e) : Inputs G e :=
  fun i => cropK F η q z (e i) (v i)
variable {A F} {ψ : ℝ → PowerSeries ℂ} (H : Canon.Physical A ψ F) (law : Scale.Law A ψ F)
section pure
variable (U : Scan G n) (V : Scan G m) (hu : InCaps d U) (hv : InCaps e V)

include law in
lemma cropK_expansion (u : Q G) (h : heft u ≤ l) :
    cropK F η q z l (cap u h) = ∑ i : Grade G (heft u), crop q z (kCue F η u (own i)) • cap (own i) (d:=l) h := by
  simp_rw [crop_eq, Finset.sum_smul, cropK, LinearMap.sum_apply, LinearMap.smul_apply,
    cap_conversion law, Finset.smul_sum]; rw [Finset.sum_comm]; simp only [smul_smul]

lemma raw_story_scan (h : Regular A) :
    PowerSeries.mk (fun k => rawCoeff A hd he (forest x (squeeze η y)) k (loadScan U hu) (loadScan V hv)) =
      party (install A) x (squeeze η y) U V := by
  ext k; rw [coeff_mk, rawCoeff_on_scan _ h]
include H law in
lemma constantCrop_expansion :
    constantCrop A η hd he x y p z (loadScan U hu) (cropArguments F η q z (loadScan V hv)) =
      ∑ j : LivesP V, (∏ i, crop q z (kCue F η (V i) (decode V j i))) *
        crop p z (party (install A) x (squeeze η y) U (decode V j)) := by
  let f := constantCrop A η hd he x y p z (loadScan U hu)
  have h (j : LivesP V) : constantCrop A η hd he x y p z (loadScan U hu) (loadScan (decode V j)
      (stillInCaps j hv)) = crop p z (party (install A) x (squeeze η y) U (decode V j)) := by
    rw [constantCrop, bothCrop_apply, raw_story_scan _ _ _ _ _ _ _ _ _ H.dimensions]
  simp_rw [← h]; change f _= ∑ j : LivesP V, _ * f _
  unfold cropArguments loadScan; simp_rw [cropK_expansion η q z law]
  rw [f.map_sum]; exact Finset.sum_congr rfl fun j _ => f.map_smul_univ _ (loadScan (decode V j) (stillInCaps j hv))
end pure

-- lift to actual arguments
section bounds
variable {I : Type} {K : Set (Points n)} {S : Set (Points m)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    {z : I → ℝ} (hz : ∀ i, |z i| ≤ 1) (hp : p ≤ q)
include law in
lemma charge_kCue {u v : Q G} : ChargeP p (-(heft u : ℝ)) (fun (_ : I) s => kCue F (-s) u v) := by
  unfold kCue; simpa only [add_zero] using (ChargeP.joint
    (show ChargeP p (-(heft u : ℝ)) (fun (_ : I) s => Acres (-s) (heft u)) from reflectV)
    (charge_cue law u v p))

variable {x : I → ↥K} {y : I → ↥S}
include H law hK hx hS hy hp hz in
lemma omitted_constantCrop (U : Scan G n) (V : Scan G m) (hu : InCaps d U) (hv : InCaps e V) :
    Omitted z p 0 (fun i s => constantCrop A (-s) hd he (x i).val (y i).val p (z i) (loadScan U hu)
      (cropArguments F (-s) q (z i) (loadScan V hv)) -
      crop p (z i) (fullSeries A F (-s) hd he (x i).val (y i).val (loadScan U hu) (loadScan V hv))) := by
  simp_rw [constantCrop_expansion _ hd he _ _ p q _ H law, fullSeries_expansion law _ hd he H.dimensions,
    map_sum, ← Finset.sum_sub_distrib, kPlay]; refine Omitted.sum _ fun j _ => ?_
  have hR := ChargeP.pull (demand_full H hK hx hS hy U (decode V j) p 0) (fun i=> (x i,y i))
  have ho := many_omitted (G:=fun i s => party (install A) (x i).val (squeeze (-s) (y i).val) U (decode V j))
    (F:=fun k (_ : I) s => kCue F (-s) (V k) (decode V j k)) (Finset.univ)
    (fun _ _ => charge_kCue _ law) hR hp hz
  rwa [Finset.sum_neg_distrib, ← Nat.cast_sum, total_h, show (∑ k, heft (V k)) = totalG V from rfl,
    neg_add_cancel] at ho

section space
-- usable also for estimating differences of observed multilinear maps.
variable (f : I → ℝ → Both G d e) {u : I → Inputs G d} {v : I → Inputs G e}
lemma expand_both (B : Both G d e) (u : Inputs G d) (v : Inputs G e) :
    B u v = ∑ a : Picks G d, multipliers u a * ∑ b : Picks G e, multipliers v b * B (basisWord a) (basisWord b) := by
  rw [basis_sum B u]; simp only [sum_apply, smul_apply, smul_eq_mul]; refine Finset.sum_congr rfl fun i _ => ?_
  congr 1; exact basis_sum _ v

lemma basis_omitted {t : ℝ} (h : ∀ a b, Omitted z p t (fun i s => f i s (basisWord a) (basisWord b))) {L : ℝ}
    (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) (hv : ∀ i, Box (v i) L) : Omitted z p t (fun i s => f i s (u i) (v i)) := by
  simp_rw [expand_both (f _ _) (u _) (v _)]; exact Omitted.sum _ fun a _ => Omitted.mul_zero_left
    (Rain.cash ⟨_, fun i => multipliers_le hL _ _ (hu i)⟩) (Omitted.sum _ fun b _ =>
      Omitted.mul_zero_left (Rain.cash ⟨_, fun i => multipliers_le hL _ _ (hv i)⟩) (h a b))

lemma basis_rain {t : ℝ} (h : ∀ a b, Rain t (fun i s => f i s (basisWord a) (basisWord b))) {L : ℝ}
    (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) (hv : ∀ i, Box (v i) L) : Rain t (fun i s => f i s (u i) (v i)) := by
  simp_rw [expand_both (f _ _) (u _) (v _)]; exact Rain.sum _ fun a _ => Rain.cover
    (Rain.cash ⟨_, fun i => multipliers_le hL _ _ (hu i)⟩) (Rain.sum _ fun b _ =>
      Rain.cover (Rain.cash ⟨_, fun i => multipliers_le hL _ _ (hv i)⟩) (h a b))
end space

def recropped (A : Arenas G) (F : ℝ → Frames G) (η : ℝ) (p q : ℕ) (z : ℝ)
    (x : Points n) (y : Points m) :=
  (MultilinearMap.compLinearMapₗ (fun i => cropK F η q z (e i))).compMultilinearMap
    (constantCrop A η hd he x y p z) - insertedCrop A F η hd he x y p z

-- NB Lean argument order hd,he before A
lemma recropped_value (z' : ℝ) (x' : Points n) (y' : Points m) :
    recropped hd he A F η p q z' x' y' u v = constantCrop A η hd he x' y' p z' u (cropArguments F η q z' v) -
        crop p z' (fullSeries A F η hd he x' y' u v) := by rw [← insertedCrop_apply]; rfl

variable {u : I → Inputs G d} {v : I → Inputs G e} {L : ℝ}
include H law hK hx hS hy hp hz in
theorem buys_recrop (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) (hv : ∀ i, Box (v i) L) :
    Omitted z p 0 (fun i s => recropped hd he A F (-s) p q (z i) (x i).val (y i).val (u i) (v i)) := by
  refine basis_omitted _ _ (fun a b => ?_) hL hu hv
  simp_rw [recropped_value]; exact omitted_constantCrop hd he p q H law hK hx hS hy hz hp
    (indexScan a) (indexScan b) (boundedByCaps a) (boundedByCaps b)
include H hK hx hS hy hz in
lemma raw_rain (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) (hv : ∀ i, Box (v i) L) :
    Rain 0 (fun i s => constantCrop A (-s) hd he (x i).val (y i).val p (z i) (u i) (v i)) := by
  refine basis_rain _ (fun a b => ?_) hL hu hv
  simp_rw [constantCrop, bothCrop_apply, basisWord, raw_story_scan _ _ _ _ _ _ _ _ _ H.dimensions]
  exact rain_crop (ChargeP.pull (ChargeP.grow (demand_full H hK hx hS hy (indexScan a) (indexScan b) p 0)
    (show (0:ℝ) ≤ (totalG (indexScan b):ℝ) from Nat.cast_nonneg _)) (fun i=> (x i,y i))) hz
end bounds
end YM.FVA2.GradedFar
