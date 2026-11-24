import YM.GradedFar.Operands
import YM.GradedFar.Vacuum

/-! Explicit checks on proper-subarray use of the price. Link two requests
at exactly the surviving points and inserting all units. -/
namespace YM.FVA2.GradedFar.Subarray
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} {N : WilsonPrescription G}
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {simple : G.Simple}
    {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)
variable {n' m' : ℕ} (a : Fin n' ↪ Fin n) (b : Fin m' ↪ Fin m)
lemma subforest (x : Points n) (y : Points m) :
    config (joint a b) (forest x y) = forest (config a x) (config b y) := by
  ext1 i; change (forest x y) (joint a b i) = _
  induction i using Fin.addCases with
    | left j => simp; rfl
    | right j => simp; rfl
def tuple (v : Inputs G d) : Inputs G (d ∘ a) := fun i => v (a i)
-- suffices also for exact Far measurements with Near singleton(s)
include H
lemma sub_applied (u : Inputs G d) (Z : Columns G e) {x : Points n} {Y : Points m} (h : forest x Y ∈ conf (n+m))
    (hu : ∀ i ∉ range a, u i = leaf G (d i))
    (hz : ∀ j ∉ range b, ∀ k, Z j k = if k=0 then leaf G (e j) else 0) (ℓ : ℕ)
    (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ) :
    applyFar (ordinary N) x Y u Z =
      applyFar (ordinary N) (config a x) (config b Y) (tuple a u) (e:=e ∘ b) (fun i => Z (b i)) := by
  have hc := (H.separatedOPE (Teller.logNu 1)).wilson.dimensions
  have h' := configuration (joint a b) h
  have h'2 : forest (config a x) (config b Y) ∈ conf _ := (subforest a b x Y) ▸ h'
  have h_eq : (⟨config (joint a b) (forest x Y),h'⟩ : Scale.Stage (n'+m')) =
      ⟨forest (config a x) (config b Y),h'2⟩ := Subtype.ext (subforest a b x Y)
  let U := installedInputs hd u
  let F k := freezeNear (book N ℓ _ ⟨forest x Y,h⟩ k) U
  let Q k := freezeNear (book N ℓ _ ⟨forest (config a x) (config b Y),h'2⟩ k) (U ∘ a)
  ext k
  rw [coeff_applyFar _ _ _ _ _ hc hd he h, coeff_applyFar (d:=d ∘ a) (e:=e ∘ b) _ _ _ _ _ hc (fun i => hd (a i)) (fun i => he (b i)) h'2]
  refine dates_kernel (V:=Normalize.leaf G ℓ) b (fun i k => up (he i) (Z i k)) ?_ F Q ?_ k
  · intro j hj k
    rw [hz j hj k]; split_ifs with he
    · rfl
    rw [map_zero]
  intro k v hv
  unfold F Q; rw [freezeNear_eq,freezeNear_eq]
  have hup (i) (hi : i ∉ range a) : U i = leaf G ℓ := by change up _ _ = _; rw [hu i hi]; rfl
  rw [book_unit H (joint a b) _ _ _ (lonely a b U v _ hup hv), h_eq, join]

lemma Yx_mask (u : Inputs G d) (v : Inputs G e) {x : Points n} {y : Points m} (s : ℝ)
    (h : forest x (squeeze (-s) y) ∈ conf (n+m))
    (hu : ∀ i ∉ range a, u i = leaf G (d i)) (hv : ∀ j ∉ range b, v j = leaf G (e j)) (ℓ : ℕ)
    (hd : ∀ i, d i ≤ ℓ) (he : ∀ i, e i ≤ ℓ) :
    Yx N T x y u v s = Yx N T (config a x) (config b y) (tuple a u) (tuple b v) s := by
  have p (j) (hj : j ∉ range b) (k) : exterior N T (-s) v j k = if k=0 then leaf G (e j) else 0 := by
    rw [exterior,hv j hj,column_unit H]
  unfold Yx
  rw [sub_applied H a b u (exterior N T (-s) v) h hu p ℓ hd he]
  have hp : config b (squeeze (-s) y) = squeeze (-s) (config b y) := by ext1 i; rfl
  rw [hp]; rfl
end
end YM.FVA2.GradedFar.Subarray
