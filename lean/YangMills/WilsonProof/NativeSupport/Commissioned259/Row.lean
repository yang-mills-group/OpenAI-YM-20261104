import YangMills.WilsonProof.NativeSupport.Commissioned259.Fare
import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Multilinear rows of the adjusted formal (ordinary!) correlation book.

Keep mixed caps; use any one common cap `H` taking those injections, not necessary to
put (e.g.) height restrictions on the Near OPE or to demand strictly positive grades/caps.
`outside` points as arguments to Row functions always mean **already dilated** (we pass `T • y`).
Zero off config (just to write the functions; not the configurations of the estimates).

Crop convention: independent coefficients in t, always taken BEFORE evaluation; in `measurement`
apply the exact running engineering × gaugeN conversion on every Far input of the adjusted book
before that crop. No expansion under *varying T*; no point displaced just for a replacement/kernel
estimate; not changing Far grade/caps or raising coupling order based on input/T.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Rake MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m H : ℕ} {R : ℝ → PowerSeries ℂ}
    (V : Arenas G) (B : ℝ → Frames G)

abbrev Slots (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Sec G (d i)
abbrev BasisSlots (G : Gauge) (d : Fin n → ℕ) := (i : Fin n) → Toon G (d i)
abbrev MLA (G : Gauge) (d : Fin n → ℕ) := MultilinearMap ℂ (fun i ↦ Sec G (d i)) ℂ

/-- `B η` here will be `GroupS.gaugeN`, `η = -log T`.
`Dial` uses length `exp(-η)`. -/
def conversion (η : ℝ) (i : ℕ) : Guard G i :=
  PowerSeries.C (Level.Dial i η) * B η i

lemma coeff_conversion (η : ℝ) (d k : ℕ) (v : Sec G d) :
    coeff k (conversion B η d) v = Level.Dial d η (coeff k (B η d) v) := by
  rw [conversion, coeff_C_mul, Module.End.mul_apply]

/-- The kernel used in this evaluation is always the one on the *prescribed* adjusted book,
`Scale.Measure.outlook`. (Here generalized over the book; identical operations below with V that
assignment.) -/
def kernel (H : ℕ) (x : Points n) (k : ℕ) : Structure1.Point G H n :=
  if h : x ∈ conf n then V H n ⟨x,h⟩ k else 0

lemma kernel_on {x : Points n} (hx : x ∈ conf n) (k H : ℕ) :
    kernel V H x k = V H n ⟨x,hx⟩ k := by rw [kernel, dif_pos hx]

lemma appendKernel_eq (f : Structure1.Point G H (n+m)) (u : Tags G H n) (v : Tags G H m) :
    (MultilinearMap.currySum (f.domDomCongr finSumFinEquiv.symm)) u v = f (Fin.append u v) := by
  change f (fun i => Sum.elim u v (finSumFinEquiv.symm i)) = _
  apply congr_arg f
  funext i
  induction i using Fin.addCases <;> simp

abbrev liftSlots {d : Fin n → ℕ} (hd : ∀ i, d i ≤ H) (u : Slots G d) : Tags G H n :=
  fun i => up (hd i) (u i)

/-- Every coefficient of the *full*, not yet marked, mixed-cap row. -/
def bareRow {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H) (he : ∀ i, e i ≤ H)
    (x : Points n) (y : Points m) (k : ℕ) :
    MultilinearMap ℂ (fun i ↦ Sec G (d i)) (MLA G e) :=
  let joint : MultilinearMap ℂ (fun _ : Fin n ↦ Sec G H) (Structure1.Point G H m) :=
    ((kernel V H (forest x y) k).domDomCongr finSumFinEquiv.symm).currySum
  ((MultilinearMap.compLinearMapₗ (fun i => up (he i)) :
    Structure1.Point G H m →ₗ[ℂ] MLA G e).compMultilinearMap joint).compLinearMap (fun i => up (hd i))

variable {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H) (he : ∀ i, e i ≤ H)
    (x : Points n) (y : Points m)

lemma bareRow_apply (k : ℕ) (u : Slots G d) (v : Slots G e) :
    bareRow V hd he x y k u v = kernel V H (forest x y) k (Fin.append (liftSlots hd u) (liftSlots he v)) := by
  change (MultilinearMap.currySum ((kernel V H (forest x y) k).domDomCongr finSumFinEquiv.symm) (liftSlots hd u) (liftSlots he v)) = _
  exact (appendKernel_eq (kernel V H (forest x y) k) (liftSlots hd u) (liftSlots he v))

abbrev kSlots (η : ℝ) (a : Days m) (v : Slots G e) : Slots G e :=
  fun i => coeff (a (some i)) (conversion B η (e i)) (v i)

/-- Insert `conversion η` before cropping, on all and only the Far slots. -/
def inserted (η : ℝ) (k : ℕ) : MultilinearMap ℂ (fun i ↦ Sec G (d i)) (MLA G e) :=
  ∑ a ∈ Normalize.tally k m,
    (MultilinearMap.compLinearMapₗ (fun i : Fin m => coeff (a (some i)) (conversion B η (e i))) :
      MLA G e →ₗ[ℂ] MLA G e).compMultilinearMap (bareRow V hd he x y (a none))

lemma inserted_apply (η : ℝ) (k : ℕ) (u : Slots G d) (v : Slots G e) :
    inserted V B hd he x y η k u v = ∑ a ∈ Normalize.tally k m,
      bareRow V hd he x y (a none) u (kSlots B η a v) := by
  rw [inserted, _root_.sum_apply, _root_.sum_apply]; rfl

def measurement (η : ℝ) (u : Slots G d) (v : Slots G e) : PowerSeries ℂ :=
  PowerSeries.mk fun k => inserted V B hd he x y η k u v

def center {h : ℕ} (hh : h ≤ H) (η : ℝ) (u : Sec G h) (v : Slots G e) : PowerSeries ℂ :=
  measurement V B (d := fun _ => h) (fun _ => hh) he (0 : Points 1) y η (fun _ => u) v

/-- Making the public operands explicit. T held fixed. All coupling coefficients at a
Far leg are of the same conversion at exactly that Far cap. -/
lemma measured_layout (hx : forest x y ∈ conf (n+m)) (η : ℝ) (u : Slots G d) (v : Slots G e) (k : ℕ) :
    coeff k (measurement V B hd he x y η u v) = ∑ a ∈ Normalize.tally k m,
      V H (n+m) ⟨forest x y,hx⟩ (a none)
        (Fin.append (liftSlots hd u) (fun i =>
          up (he i) (coeff (a (some i)) (conversion B η (e i)) (v i)))) := by
  simp_rw [measurement, coeff_mk, inserted_apply, bareRow_apply, kernel_on V hx] 

/-- Exact basis tools for those mixed caps (keep true engineering sizes). -/
def coordinates (b : BasisSlots G d) (u : Slots G d) : ℂ :=
  ∏ i, coord (b i) (u i)
abbrev word (b : BasisSlots G d) : Slots G d := fun i => theory (b i)
abbrev names (b : BasisSlots G d) : Scan G n := fun i => flash (b i)
abbrev Balls (L : ℝ) (G : Gauge) (d : Fin n → ℕ) : Set (Slots G d) :=
  {u | ∀ i j, ‖coord j (u i)‖ ≤ L}

lemma coord_price {L : ℝ} (_hL : 0 ≤ L) (u : Slots G d) (hu : u ∈ Balls L G d) (b : BasisSlots G d) :
    ‖coordinates b u‖ ≤ L^n := by
  rw [coordinates, norm_prod]
  calc
    _ ≤ ∏ _i : Fin n, L := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hu i _)
    _ = L^n := by simp

lemma word_sigma {E : Type*} [AddCommMonoid E] [Module ℂ E] (u : Slots G d)
    (X : MultilinearMap ℂ (fun i ↦ Sec G (d i)) E) :
    X u = ∑ b : BasisSlots G d, coordinates b u • X (word b) := by
  have hu (i : Fin n) : (∑ c : Toon G (d i), coord c (u i) • theory c) = u i := all_sig (u i)
  have hh := X.map_sum (fun i (j : Toon G (d i)) => coord j (u i) • theory j)
  simp_rw [hu] at hh
  exact hh.trans (Finset.sum_congr rfl (fun b _ => X.map_smul_univ _ (word b)))

/-- Multilinear inner-profile extension of the actual continuum `FarCoefficients`: return
components on the output alphabet. -/
def farCf (u : Slots G d) (x : Points n) (q : Q G) : PowerSeries ℂ :=
  ∑ b : BasisSlots G d, PowerSeries.C (coordinates b u) * FarCoefficients V (names b) x q

/-- Crop as a linear map (inclusive of `p`); only *finite polynomial* evaluation. -/
def crop (p : ℕ) (t : ℝ) : PowerSeries ℂ →ₗ[ℂ] ℂ :=
  ∑ k ∈ Finset.range (p+1), (t:ℂ)^k • coeff (R:=ℂ) k

lemma crop_apply (p : ℕ) (t : ℝ) (f : PowerSeries ℂ) :
    crop p t f = ∑ k ∈ Finset.range (p+1), (t:ℂ)^k * coeff k f := by
  rw [crop, LinearMap.sum_apply]; rfl

/-- Actual argument `c` to the (through-h) response in (M.2): a separately cropped vector
on the SAME alphabet. -/
def purchased (u : Slots G d) (x : Points n) (h p : ℕ) (t : ℝ) : Sec G h :=
  ∑ q : Toon G h, crop p t (farCf V u x (flash q)) • theory q

end YM.FVA2.GradedFar259
