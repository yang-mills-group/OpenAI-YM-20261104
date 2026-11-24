import YM.Integration.WilsonTrueProjectedPointProgram

/-! Inverse normalization for the independent numerical field along its actual
child itinerary.  Rescale each filed transfer by its own measured coupling
before composing.  The same matrix is used at both ends of every edge. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointInverse
open Function Finset Matrix PowerSeries Lattice Wilson RG Labels Source Trace.Physical
open FormalBulk08 City Pose PhysicalNext Repeat Legato
open WilsonTrueProjectedFiledTransfer WilsonTrueProjectedPointProgram
open scoped Classical BigOperators PowerSeries
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
variable (wood : Primer.Families R.family) (a : hue G) (depth : d < D)
    (digit : ∀ i, Site (R.family.S.block i))
local notation "A" => WilsonNeutralPointCourse.transfer R wood a depth digit

def clockMap (g : ℝ) := (PowerSeries.map Complex.ofRealHom).comp (PowerSeries.rescale g)

def up (N j : ℕ) (g : ℝ) : Matrix ι ι (PowerSeries ℂ) :=
  (clockMap g).mapMatrix ((A N j)⁻¹)
def down (N j : ℕ) (g : ℝ) : Matrix ι ι (PowerSeries ℂ) :=
  (clockMap g).mapMatrix (A N j)

theorem term_at (N j : ℕ) (g : ℝ) (n : ℕ) (u b : ι) :
    coeff n (down R wood a depth digit N j g u b) = term R wood a depth digit N j g n u b := by
  change coeff n ((PowerSeries.map Complex.ofRealHom) ((rescale g) (A N j u b))) = _
  rw [coeff_map,coeff_rescale]
  rfl

theorem inverse (N j : ℕ) (g : ℝ) (simple : G.Simple) (o : Stationary.Loc G 1)
    (live : j < N) (front : d ≤ R.family.path.levels.clock.J (j+1)) :
    down R wood a depth digit N j g * up R wood a depth digit N j g = 1 := by
  have valid := (WilsonNeutralPointCourse.received R wood a depth digit N j simple o live front).1.det
  exact (map_mul ..).symm.trans ((congrArg (clockMap g).mapMatrix (Matrix.mul_nonsing_inv _ valid)).trans (map_one _))

def take (q : ℕ) (v : ι → PowerSeries ℂ) (k : Fin (q+1)) (b : ι) : ℂ := coeff k.val (v b)

private theorem collect {q : ℕ} (k e : Fin (q+1)) (b : ℕ → ℂ) :
    (∑ n : Fin (q-k.val+1), if e = WilsonTrueProjectedFiledGrades.degree k n then b n.val else 0) =
      if k.val ≤ e.val then b (e.val-k.val) else 0 := by
  by_cases h : k.val ≤ e.val
  · rw [if_pos h]
    let n : Fin (q-k.val+1) := ⟨e.val-k.val,by have := e.isLt; omega⟩
    rw [Finset.sum_eq_single n]
    · rw [if_pos]
      apply Fin.ext
      change e.val = k.val + (e.val-k.val)
      omega
    · intro n' _ hn'
      apply if_neg
      intro same
      have hit := congrArg Fin.val same
      change e.val = k.val+n'.val at hit
      apply hn'
      apply Fin.ext
      change n'.val = e.val-k.val
      omega
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro n _
    apply if_neg
    intro same
    have hit := congrArg Fin.val same
    change e.val = k.val+n.val at hit
    omega

private theorem clip (q e : ℕ) (hq : e ≤ q) (f : ℕ → ℂ) :
    (∑ k : Fin (q+1), if k.val ≤ e then f k.val else 0) = ∑ k ∈ Finset.range (e+1), f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ e then f k else 0) (q+1)]
  rw [←Finset.sum_subset (s₁:=Finset.range (e+1)) (Finset.range_mono (Nat.succ_le_succ hq))
    (fun k _ hk => if_neg (by simpa [Nat.lt_succ_iff] using hk))]
  apply Finset.sum_congr rfl
  intro k hk
  exact if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

theorem coefficients (N j q : ℕ) (g : ℝ) (v : ι → PowerSeries ℂ) :
    layer R wood a depth digit N j q g (take R q v) =
      take R q ((down R wood a depth digit N j g) *ᵥ v) := by
  funext e u
  let f (k : ℕ) := moved R (term R wood a depth digit N j g (e.val-k)) (fun b => coeff k (v b)) u
  change (∑ k : Fin (q+1), ∑ n : Fin (q-k.val+1), if e=WilsonTrueProjectedFiledGrades.degree k n
    then moved R (term R wood a depth digit N j g n.val) (fun b => coeff k.val (v b)) u else 0) = _
  rw [Finset.sum_congr rfl (fun (k : Fin (q+1)) _ => collect k e
    (fun n => moved R (term R wood a depth digit N j g n) (fun b => coeff k.val (v b)) u))]
  change (∑ k : Fin (q+1), if k.val ≤ e.val then f k.val else 0) = _
  rw [clip q e.val (Nat.le_of_lt_succ e.isLt)]
  change _ = coeff e.val (∑ b, down R wood a depth digit N j g u b * v b)
  simp only [map_sum, mul_comm (down R wood a depth digit N j g u _) (v _),coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,term_at]
  rw [Finset.sum_comm]
  rfl

def lift (N first : ℕ) (g : ℕ → ℝ) (report : ι → PowerSeries ℂ) : ℕ → ι → PowerSeries ℂ
  | 0 => report
  | n+1 => up R wood a depth digit N (first+n) (g (first+n)) *ᵥ lift N first g report n

/-- The normalized numerical input at any age uses inverse factors only
between that age and the report. This holds for the exact independent
vectors before assigning their magnitude or fitting any physical raw field. -/
theorem original (N first q : ℕ) (g : ℕ → ℝ) (report : ι → PowerSeries ℂ)
    (simple : G.Simple) (o : Stationary.Loc G 1) (front : d ≤ R.family.path.levels.clock.J (first+1))
    (j : ℕ) (start : first ≤ j) (live : j ≤ N) :
    income R wood a depth digit N N q g (take R q (lift R wood a depth digit N first g report (N-first))) j =
      take R q (lift R wood a depth digit N first g report (j-first)) := by
  induction live using Nat.decreasingInduction with
  | self => simp [income,walk]
  | of_succ j hj ih =>
    rw [previous R wood a depth digit N N q g _ hj,ih (start.trans (Nat.le_succ _))]
    rw [show j+1-first = j-first+1 by omega]
    simp only [lift,show first+(j-first)=j by omega]
    rw [coefficients,Matrix.mulVec_mulVec,inverse R wood a depth digit N j (g j) simple o hj
      (front.trans (R.family.path.levels.fits.mono (Nat.succ_le_succ start))),Matrix.one_mulVec]

end YM.Integration.WilsonTrueProjectedPointInverse
