import YM.WilsonMS.Scales.StairBounds
import YM.XSpace.Welcome
/-!
# Point-wise estimates after exact-regulator frame cancellation

Enough also on cube of payouts in the detector (products of point reports
kept at a fixed locus). Expose the prepared continuum prediction and its
independent pinned kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FrameConj
open Function Set Filter MeasureTheory Real Finset Metric
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1 Lattice
open Maxwell Maxwell.Free Maxwell.Wick VisitH
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu Rider Reservoir VisitH Sea Fray
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n j k : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
variable {K : Set (Points n)}

abbrev pι (A : Prescription (Ensure.deck G)) (μ : ℝ) (p : XSpace.Mesh) :=
  Program.shift A.team (μ - height p)
namespace Gates
variable {X : Sample n → Point G d n} {P : Points n → Point G d n}

abbrev Cert (X : Cirrus.Sample n → Point G d n) (P : Points n → Point G d n) (K : Set (Points n)) :=
  ∀ v : Fin n → Glyph BΨ d, Vitals (fun t => X t (glow ∘ v)) (fun x => P x (glow ∘ v)) K

lemma vPaid (H : Cert X P K) {t : 𝕄 → Fin n → Sec G d} {v : Fin n → Sec G d}
    (u : ∀ i, Follows (fun p => t p i) (v i)) : Vitals (fun i => X i (t i.F)) (fun i => P i v) K := by
  let B := Daylight BΨ d
  have he (X : Point G d n) (p : Fin n → Sec G d) :
    X p = ∑ i : Fin n → Glyph BΨ d, (∏ j, B.coord (i j) (p j)) * X (glow ∘ i) := fromHeight ..
  simp_rw [he (X _) (t _), he (P _) v]
  apply Vitals.sum
  intro i _
  have hp :=
    Fast.p_prod (f := fun j p => B.coord (i j) (t p j)) (x := fun j => B.coord (i j) (v j))
      Finset.univ (fun j _ => Follows.run (u j) (i j))
  exact (Vitals.confirm hp).team (H i)

lemma liftT {X : Sample n → Octave G d n} {P : Points n → Octave G d n}
    (h : ∀ i ≤ j, Cert (fun x => X x i) (fun x => P x i) K) (T : 𝕄 → Guard G d) (S : Guard G d)
    (he : ∀ i ≤ j, Fell (fun x => coeff i (T x)) (coeff i S)) :
    ∀ v : Fin n → Sec G d, Vitals (fun x => pivot (T x.F) (X x) j v) (fun x => pivot S (P x) j v) K := by
  intro v
  simp_rw [pivot_cost]
  apply Vitals.sum
  intro u hu
  have ht (x : Option (Fin n)) : u x ≤ j :=
    le_trans (Finset.single_le_sum (f := fun k => u k) (fun i _ => Nat.zero_le _) (Finset.mem_univ x))
      (totaled u |>.mp hu).le
  exact vPaid (h _ (ht none)) (u := fun i => he (u (some i)) (ht _) (v i))
variable (W : Initialize G) (Q : Store G) (A : Prescription (Ensure.deck G)) (μ : ℝ)
local notation "rη" => pι A μ

def refinedP (d : ℕ) (p : Sample n) :=
  pivot (Fiscal.bets A (μ - height p.F) (height p.F) d) (Program.substitute (rη p.F) (live W d p))

lemma noteKing (p : Sample n) (v : Fin n → Glyph BΨ d) (j : ℕ) :
    refinedP W A μ d p j (glow ∘ v) = note W μ A v p j := by
  have hx (t : Fin n → Sec G d) (i : ℕ) :
    substitute (rη p.F) (live W d p) i t =
      coeff i (Coupling.composeS (rη p.F) (point W p.F d (chartV p) t)) := by
    rw [bookCost]
    obtain h : (fun j => live W d p j t) = Coupling.read (point W p.F d (chartV p) t) :=
      funext (fun j => Eq.trans (Rose.lit_up W d p t j) rfl)
    rw [h]
    exact congr_fun (Coupling.explicit (share ..) _) i
  unfold refinedP
  rw [pivot_cost]
  simp_rw [hx]
  unfold VisitH.note
  rw [paid_height W μ A v p.layout p.F 0]
  exact pulse_point A W p.F (μ - height p.F) (height p.F) v p.layout (small_p _) 0 j _ rfl
variable {M : Booked (Ensure.deck G)} (F : MS_Data G M)
variable (H : G.Simple) (h : Installed W F A) (u : Rider.Commuting A)
include H h

lemma climb_final (hp : IsCompact K) (hx : K ⊆ conf n) (d j : ℕ) :
    Cert (fun i : Sample n => refinedP W A μ d i j) (fun x : Points n => lowKernel F μ j d x) K := by
  intro v
  simp_rw [noteKing, lowK]
  obtain ⟨C, hC, hV⟩ := picture W μ A v K F H h hp hx j
  refine ⟨?_, Tide.mildG, Tide.mild_p, C, hC, hV⟩
  obtain ⟨⟨A, hA, hp'⟩, a, ha, D, hD, h⟩ := answers_cost v F μ j hp hx
  refine ⟨⟨A, hA, 0, fun i t p => ?_⟩, a, ha, D, hD, 0, ?_⟩
  · simp only [pow_zero, Pi.one_apply, mul_one]
    exact hp' _ i.property
  intro i j r hr hi t p
  simp only [pow_zero, Pi.one_apply, mul_one]
  exact h _ i.property _ j.property r hr hi
omit H h

def Lμ (μ : ℝ) (d : ℕ) :=
  (Q.survey d).Lays (Q.prepared d) (fun i => Continuum F μ i d)

def Thaw (μ : ℝ) (d : ℕ) (x : Points n) :=
  pivot (deck (Lμ Q F μ d)) (fun i => lowKernel F μ i d x)

def thawed (μ : ℝ) (d : ℕ) :=
  realm (deck (Lμ Q F μ d)) (fun i => Continuum F μ i d)

lemma theorem_F (d n : ℕ) : FundsK (fun x : Points n => Thaw Q F μ d x) (thawed Q F μ d) :=
  pivotFund (F := fun x i => lowKernel F μ i d x)
    (fun i p => ⟨smooth_read F μ i p, fun _ => continues ..⟩) _

lemma cooks (d : ℕ) (x : Sample n) :
    Rose.cooked W Q d x = pivot (deck (Q.layout W (grab x) d)) (live W d x) :=
  rfl
include H h u

/-- Rate certificate on the shifted, position-normalized columns. -/
lemma picture_cost (hp : IsCompact K) (hx : K ⊆ conf n) (d j : ℕ) (v : Fin n → Sec G d) :
    Vitals (fun x => Program.substitute (rη x.F) (Rose.cooked W Q d x) j v)
      (fun x => Thaw Q F μ d x j v) K := by
  let T i := (Q.survey d).Lays (Q.prepared d) (amended W μ A i d)
  have he (i : ℕ) : Fell (fun x => coeff i (deck (T x))) (coeff i (deck (Lμ Q F μ d))) := by
    let G' (i : ℕ) := Continuum F μ i d
    apply Fell.guard (v := Lμ Q F μ d)
    exact
      route_higher (Q.prepared d) (Q.survey d) ((free_match F μ d) ▸ order_rates H h μ d 0)
        (free_match F μ d) (F := fun x => amended W μ A x d) (P := G') i
        (fun i _ => order_rates H h μ d i)
  apply
    Vitals.exact_s
      (liftT (X := fun x => refinedP W A μ d x) (P := fun x i => lowKernel F μ i d x) (j := j)
        (fun i _ => climb_final W A μ F H h hp hx _ i) (fun x => deck (T x)) (deck (Lμ Q F μ d))
        (fun i _ => he i) v)
  filter_upwards [exact_breg μ Q H h u d] with i hi x hF
  rw [← hF] at hi
  rw [refinedP, point_times, cooks, pointMove (share A.team (μ - height x.F)), pι, hi]
end Gates
end YM.WilsonMS.FrameConj
