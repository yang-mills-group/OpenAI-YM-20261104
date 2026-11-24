import YM.Integration.WilsonTrueProjectedTriangularFare

/-! Polynomial cost of the remaining inverse between a report and a fixed
age. The rank on numerical coefficients uses the actual Colfax priority
and the coupling grade. This estimate precedes fitting the physical axes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointSalary
open Function Finset Matrix PowerSeries Lattice Wilson RG Labels Source Trace.Physical
open FormalBulk08 City Pose PhysicalNext Repeat Legato
open WilsonTrueProjectedPointInverse
open scoped Classical BigOperators PowerSeries
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
variable (wood : Primer.Families R.family) (a : hue G) (depth : d < D)
    (digit : ∀ i, Site (R.family.S.block i))
local notation "A" => WilsonNeutralPointCourse.transfer R wood a depth digit

def entry (N j : ℕ) (g : ℝ) (n : ℕ) (u b : ι) : ℝ :=
  g^n * coeff n ((A N j)⁻¹ u b)

theorem up_at (N j : ℕ) (g : ℝ) (n : ℕ) (u b : ι) :
    coeff n (up R wood a depth digit N j g u b) = (entry R wood a depth digit N j g n u b:ℂ) := by
  change coeff n ((PowerSeries.map Complex.ofRealHom) ((rescale g) ((A N j)⁻¹ u b)))=_
  rw [coeff_map,coeff_rescale]
  rfl

abbrev Panel (q : ℕ) := Fin (q+1) × ι

def readout (q : ℕ) (v : ι → PowerSeries ℂ) (z : Panel R (d:=d) q) : ℂ :=
  coeff z.1.val (v z.2)

def bill (N j q : ℕ) (g : ℝ) (z y : Panel R (d:=d) q) : ℂ :=
  if y.1.val ≤ z.1.val then (entry R wood a depth digit N j g (z.1.val-y.1.val) z.2 y.2:ℂ) else 0

private theorem cut (q e : ℕ) (hq : e ≤ q) (f : ℕ → ℂ) :
    (∑ k : Fin (q+1), if k.val ≤ e then f k.val else 0) = ∑ k ∈ range (e+1), f k := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ e then f k else 0) (q+1)]
  rw [←Finset.sum_subset (s₁:=range (e+1)) (range_mono (Nat.succ_le_succ hq))
    (fun k _ hk => if_neg (by simpa [Nat.lt_succ_iff] using hk))]
  exact sum_congr rfl fun k hk => if_pos (Nat.le_of_lt_succ (mem_range.mp hk))

theorem representation (N j q : ℕ) (g : ℝ) (v : ι → PowerSeries ℂ) :
    readout R q ((up R wood a depth digit N j g) *ᵥ v) =
      (bill R wood a depth digit N j q g) *ᵥ readout R q v := by
  funext ⟨e,u⟩
  change coeff e.val (∑ b, up R wood a depth digit N j g u b*v b) = ∑ y, _
  simp only [map_sum,mul_comm (up R wood a depth digit N j g u _) (v _),coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,up_at,Fintype.sum_prod_type]
  rw [Finset.sum_comm (s:=univ (α:=Fin (q+1)))]
  apply sum_congr rfl
  intro b _
  let f (k : ℕ) := coeff k (v b) * (entry R wood a depth digit N j g (e.val-k) u b:ℂ)
  rw [←cut q e.val (Nat.le_of_lt_succ e.isLt) f]
  apply sum_congr rfl
  intro k _
  by_cases lower : k.val≤e.val
  · simp only [lower,if_pos,bill,readout,f,mul_comm]
  · simp only [lower,if_false,bill,zero_mul]

def level (q : ℕ) (z : Panel R (d:=d) q) :=
  let c := Fintype.card ι
  let row := Roof.priority (slots (R.family.labels.level d)) (Pose.weight (R.family.labels.level d))
  (c+1)*z.1.val+(c-row z.2)

theorem strict (N j q : ℕ) (g : ℝ) (simple : G.Simple) (o : Stationary.Loc G 1)
    (live : j<N) (front : d ≤ R.family.path.levels.clock.J (j+1))
    (z y : Panel R (d:=d) q) (different : z≠y) (used : bill R wood a depth digit N j q g z y ≠0) :
    level R q y < level R q z := by
  classical
  rcases z with ⟨e,u⟩
  rcases y with ⟨k,b⟩
  change (if k.val≤e.val then (entry R wood a depth digit N j g (e.val-k.val) u b:ℂ) else 0) ≠ 0 at used
  split at used
  · rename_i order
    let c := Fintype.card ι
    let row := Roof.priority (slots (R.family.labels.level d)) (Pose.weight (R.family.labels.level d))
    have cap (x : ι) : row x ≤ c := Finset.card_le_univ _
    change (c+1)*k.val+(c-row b) < (c+1)*e.val+(c-row u)
    rcases lt_or_eq_of_le order with less|same
    · have stair := Nat.mul_le_mul_left (c+1) (Nat.succ_le_of_lt less)
      rw [Nat.mul_succ] at stair
      omega
    · have diff : u≠b := fun h => different (Prod.ext (Fin.ext same.symm) h)
      have nonzero : coeff 0 ((A N j)⁻¹ u b) ≠ 0 := by
        intro hz
        apply used
        simp [entry,same,hz]
      have native := (WilsonNeutralPointCourse.received R wood a depth digit N j simple o live front).1.back
      have promoted : row u < row b := Roof.promotes (native.peers u b nonzero diff)
      have bounded := cap b
      rw [same]
      omega
  · exact (used rfl).elim

theorem diagonal (N j q : ℕ) (g : ℝ) (simple : G.Simple) (o : Stationary.Loc G 1)
    (live : j<N) (front : d ≤ R.family.path.levels.clock.J (j+1))
    (z : Panel R (d:=d) q) : ‖bill R wood a depth digit N j q g z z‖ ≤ 1 := by
  rcases z with ⟨e,u⟩
  have native := (WilsonNeutralPointCourse.received R wood a depth digit N j simple o live front).1.back
  have L : (1:ℝ) ≤ ((R.family.S.block j).val:ℝ) := by exact_mod_cast (R.family.S.block j).pos
  have h : (1:ℝ) ≤ ((R.family.S.block j).val:ℝ)^(d-Pose.weight (R.family.labels.level d) u) := one_le_pow₀ L
  simp only [bill,le_refl,if_pos,Nat.sub_self,entry,pow_zero,one_mul,Complex.norm_real,
    Real.norm_eq_abs,native.due,Grail.heightK_of_le _ (weightFits _ u)]
  rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans h))]
  exact inv_le_one_of_one_le₀ h

/-- Only the bounded single-step inverse through the retained grades enters H. -/
theorem original (N first n q : ℕ) (g : ℕ → ℝ) (report : ι → PowerSeries ℂ)
    (simple : G.Simple) (o : Stationary.Loc G 1) (front : d ≤ R.family.path.levels.clock.J (first+1))
    (live : first+n≤N) {H B : ℝ} (hp : 0≤H) (fund : 0≤B)
    (start : ∀ b, ‖readout R q report b‖≤B)
    (fare : ∀ i, i<n → ∀ k, k≤q → ∀ u b,
      |entry R wood a depth digit N (first+i) (g (first+i)) k u b| ≤ H)
    (z : Panel R (d:=d) q) :
    ‖readout R q (lift R wood a depth digit N first g report n) z‖ ≤
      B*(1+(Fintype.card (Panel R (d:=d) q):ℝ)*H*n)^(level R q z) := by
  let stepAt (i : ℕ) := bill R wood a depth digit N (first+i) q (g (first+i))
  let v (i : ℕ) := readout R q (lift R wood a depth digit N first g report i)
  have afford (i : ℕ) : d ≤ R.family.path.levels.clock.J ((first+i)+1) :=
    front.trans (R.family.path.levels.fits.mono (by omega))
  suffices ans : ‖v (0+n) z‖ ≤ B*(1+(Fintype.card (Panel R (d:=d) q):ℝ)*H*n)^(level R q z) by
    simpa only [Nat.zero_add,v] using ans
  apply WilsonTrueProjectedTriangularFare.window (level R q) stepAt v 0 n H B hp fund start
  · intro i _ _
    exact representation R wood a depth digit N _ q _ _
  · intro i _ end' u
    exact diagonal R wood a depth digit N (first+i) q _ simple o (by omega) (afford i) u
  · intro i _ end'
    exact strict R wood a depth digit N (first+i) q _ simple o (by omega) (afford i)
  · intro i _ end' u b
    dsimp only [stepAt,bill]
    split
    · rw [Complex.norm_real,Real.norm_eq_abs]
      exact fare i (by omega) _ (by have := u.1.isLt; omega) u.2 b.2
    · simpa using hp

end YM.Integration.WilsonTrueProjectedPointSalary
