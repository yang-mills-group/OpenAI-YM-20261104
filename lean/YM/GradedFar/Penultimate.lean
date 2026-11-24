import YM.GradedFar.Uniform
import YM.GradedFar.Crop
/-!
# The estimate at any evaluation parameter in the unit disk (real axis)

Work to higher than retained degree when estimating product terms: the right side also must
work with the actual **separately cropped** FarCoefficients vector passed to the response row.
Thus an aligned product through p does *not* compute the subtraction we want. Here we price
every additional term. Logarithmic input `s = log T`. Evaluation `z` is independent; actual
(t(r), g) comparison follows in the application.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

section crop_expenses
variable {I : Type} {F G : I → ℝ → PowerSeries ℂ} {z : I → ℝ} {a : ℝ} {p : ℕ}

lemma clock_cash (hz : ∀ i, |z i| ≤ 1) (k : ℕ) : Rain 0 (fun i (_ : ℝ) => (z i : ℂ)^k) := by
  refine Rain.powers (f:=fun i (_ : ℝ) => (z i : ℂ)) (Rain.cash ⟨1, fun i => ?_⟩) k
  rw [Complex.norm_real,Real.norm_eq_abs]; apply hz

lemma rain_crop (h : ChargeP (p+1) a F) (hz : ∀ i, |z i| ≤ 1) :
    Rain a (fun i s => crop p (z i) (F i s)) := by
  simp_rw [crop_eq]; exact Rain.sum _ fun j hj => Rain.cover (clock_cash hz j)
    (h j (Finset.mem_range.mp hj))

lemma rain_overrun (hF : ChargeP (p+1) 0 F) (hG : ChargeP (p+1) a G) (hz : ∀ i, |z i| ≤ 1) :
    Rain a (fun i s => overrun p (z i) (F i s) (G i s)) := by
  unfold overrun; refine Rain.sum _ fun j hj => ?_
  obtain ⟨h,h',_⟩ := skipped_spec j hj
  exact Rain.cover (clock_cash hz _) (Rain.cover (hF j.1 h) (hG j.2 h'))
end crop_expenses

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
variable (A : Arenas G) (F : ℝ → Frames G)
    (hd : Through l d) (he : Through l e)
    (hh : h ≤ l) (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e)

section vector
/-- `c` in (M.1). Evaluated with separate crop; a vector in the actual output alphabet. -/
def croppedVector (h : ℕ) (p : ℕ) (u : Inputs G d) (x : Points n) (z : ℝ) : Sec G h :=
  ∑ q : Toon G h, crop p z (ope A u x (Dframe.flash q)) • theory q

/-- order k coefficient of the vector-valued formal series through output h. -/
def opeVector (h : ℕ) (u : Inputs G d) (x : Points n) (k : ℕ) : Sec G h :=
  ∑ q : Toon G h, coeff k (ope A u x (Dframe.flash q)) • theory q
lemma croppedVector_series (p h : ℕ) (t : ℝ) : croppedVector A h p u x t =
    ∑ k ∈ Finset.range (p+1), (t:ℂ)^k • opeVector A h u x k := by
  unfold croppedVector opeVector; simp_rw [crop_eq, Finset.sum_smul, Finset.smul_sum, smul_smul]; rw [Finset.sum_comm]

-- helper to use replacement as an actual operator, not just a family of readings
def atInputs (u : Inputs G d) : (MultilinearMap ℂ (fun i => Sec G (d i)) ℂ) →ₗ[ℂ] ℂ where
  toFun f := f u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def response (F' : Both G (Output h) e) (v : Inputs G e) : Sec G h →ₗ[ℂ] ℂ :=
  (atInputs v).comp (F'.toLinearMap 0 0)
lemma response_apply (F' : Both G (Output h) e) (v : Inputs G e) (a : Sec G h) :
    response F' v a = F' (fun _ => a) v := by
  change F' (Function.update _ 0 a) v = _
  congr 2; funext i; fin_cases i; simp

def responseCoeff (η : ℝ) (hh : h ≤ l) (he : Through l e) (y : Points m) (v : Inputs G e) (k : ℕ) :=
  response (withFar A (conversion F η) (d:=Output h) (fun _ => hh) he (outgoing (squeeze η y)) k) v
lemma responseCoeff_apply (η : ℝ) (k : ℕ) (a : Sec G h) : responseCoeff A F η hh he y v k a =
    coeff k (replacementSeries A F η hh he y a v) := by
  rw [replacementSeries, fullSeries, coeff_mk, responseCoeff, response_apply]

/-- Cropping the operator series `[D^X]_{≤p}`. -/
def croppedResponse (η : ℝ) (hh : h ≤ l) (he : Through l e) (y : Points m) (v : Inputs G e)
    (p : ℕ) (z : ℝ) := ∑ k ∈ Finset.range (p+1), (z:ℂ)^k • responseCoeff A F η hh he y v k
lemma croppedResponse_apply (η : ℝ) (p : ℕ) (z : ℝ) (a : Sec G h) :
    croppedResponse A F η hh he y v p z a = crop p z (replacementSeries A F η hh he y a v) := by
  simp_rw [croppedResponse, crop_eq, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, responseCoeff_apply]
end vector

/-- The signed/complex comparison of the two separately evaluated operands. -/
def difference (η : ℝ) (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) (p : ℕ) (z : ℝ) : ℂ :=
  crop p z (fullSeries A F η hd he x y u v) - croppedResponse A F η hh he y v p z
    (croppedVector A h p u x z)

def overruns (η : ℝ) (he : Through l e) (hh : h ≤ l)
    (x : Points n) (y : Points m) (u : Inputs G d) (v : Inputs G e) (p : ℕ) (z : ℝ) :=
  ∑ q : Toon G h, overrun p z (ope A u x (Dframe.flash q)) (replacementSeries A F η hh he y (theory q) v)

lemma comparison_split (η : ℝ) (p : ℕ) (z : ℝ) :
    difference A F η hd he hh x y u v p z = crop p z (tailSeries A F η hd he hh x y u v) -
      (z:ℂ)^(p+1) * overruns A F η he hh x y u v p z := by
  unfold difference croppedVector; rw [map_sum]; simp_rw [_root_.map_smul, smul_eq_mul,
    croppedResponse_apply, separate]
  unfold tailSeries overruns; rw [Finset.sum_add_distrib, map_sub, map_sum, Finset.mul_sum]; abel

section uniform
variable {A F} {ψ : ℝ → PowerSeries ℂ} (H : Canon.Physical A ψ F) (law : Scale.Law A ψ F)
    {K : Set (Points n)} {S : Set (Points m)} (hK : IsCompact K) (hx : K ⊆ conf n)
    (hS : IsCompact S) (hy : S ⊆ Outside m)

include H law hK hx hS hy
lemma rain_overruns (p : ℕ) {I : Type} {x : I → ↥K} {y : I → ↥S} {u : I → Inputs G d} {v : I → Inputs G e}
    {L : ℝ} (hL : 0 ≤ L) (hu : ∀ i, Box (u i) L) (hv : ∀ i, Box (v i) L)
    {z : I → ℝ} (hz : ∀ i, |z i| ≤ 1) :
    Rain 0 (fun i s => overruns A F (-s) he hh (x i).val (y i).val (u i) (v i) p (z i)) := by
  refine Rain.sum _ fun q _ => rain_overrun (fun k _ => ?_) ?_ hz
  · obtain ⟨C,hC⟩ := uniform_opeCoeff (d:=d) H hK hx (Dframe.flash q) k hL
    exact Rain.cash ⟨ C, fun i => hC _ (x i).property (u i) (hu i)⟩
  exact ChargeP.grow (uniform_replacement_charge (y:=y) H law hS hy he hh p q hL hv)
    (show (0:ℝ) ≤ (heft (Dframe.flash q) : ℝ) from Nat.cast_nonneg _)

-- Bundle *all* pointwise parameters. This will give an estimate with arbitrary meshes or tests tuning
-- their evaluation parameter, provided only the ball conditions at each T. No product measures!
structure Domain (d : Fin n → ℕ) (e : Fin m → ℕ) (G : Gauge) (K : Set (Points n)) (S : Set (Points m))
    (L : ℝ) where
  x : ↥K
  y : ↥S
  u : Inputs G d
  v : Inputs G e
  hu : Box u L
  hv : Box v L
  z : ℝ
  hz : |z| ≤ 1

lemma log_time_budget (p : ℕ) {L : ℝ} (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∀ᶠ s in atTop,
    ∀ i : Domain d e G K S L, ‖difference A F (-s) hd he hh i.x.val i.y.val i.u i.v p i.z‖ ≤
      C * (Real.exp (-((h:ℝ)+1)*s) + |i.z|^(p+1)) * (1+s)^k := by
  let I := Domain d e G K S L
  obtain ⟨C,hC,k,hi⟩ := rain_crop (uniform_tail_charge (I:=I) (x:=Domain.x) (y:=Domain.y)
    H law hK hx hS hy hd he p hh hL Domain.hu Domain.hv) Domain.hz
  obtain ⟨D,hD,j,hj⟩ := rain_overruns he hh H law hK hx hS hy p (I:=I) (x:=Domain.x) (y:=Domain.y)
    hL Domain.hu Domain.hv Domain.hz
  refine ⟨C+D, add_pos hC hD, k+j, ?_⟩
  filter_upwards [hi,hj,eventually_ge_atTop (0:ℝ)] with s hs ho hs0 i
  rw [comparison_split]
  apply (norm_sub_le ..).trans; rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  refine (add_le_add (hs i) (mul_le_mul_of_nonneg_left (ho i) (by positivity))).trans ?_
  unfold post; rw [neg_zero, zero_mul, Real.exp_zero, mul_one]
  have hu : 1 ≤ 1+s := by linarith
  calc
    _ ≤ (C+D)*((1+s)^(k+j) * Real.exp (-((h:ℝ)+1)*s)) + |i.z|^(p+1)*((C+D)*(1+s)^(k+j)) := by gcongr <;> linarith
    _ = _ := by ring
end uniform
end YM.FVA2.GradedFar
