import YM.Integration.FVA1Physical.Wilson.RootedToll

/-! Interior-to-bulk comparison of the full, spatially distributed conditional
Wilson action. The marked and unmarked series use the same inverse covariance
and the same incoming scene. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Lapaz
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G : Gauge}

def bulkPoint (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) :=
  meetVar (A.fClock⁻¹ • z) (A.fClock⁻¹ • bulkCoordinate A z)

def innerPoint (A : Mosaic.Issue G) (J:Voice G) (y : ℝ) (z:Positions (Primary A.c G)) (b:Site A.f)
    (U : Config G A.f) :=
  meetVar (A.fClock⁻¹ • z) (A.fClock⁻¹ • interiorCoordinate A J y z b U)

def bulkColumn (A : Mosaic.Issue G) (χ : ChartRatio G) (z : Positions (Primary A.c G))
    (src : PowerSeries (Pot (Joint A.F G))) (p : ℕ) :=
  Lapaz.owes (Rolling.straight A.F G) ((mold A.pre A.F A.v)⁻¹)
    (barbed A.F A.v χ A.T) src (bulkPoint A z) p

def innerColumn (A : Mosaic.Issue G) (χ : ChartRatio G) (J:Voice G) (y : ℝ) (z : Positions (Primary A.c G))
    (b:Site A.f) (U:Config G A.f) (src : PowerSeries (Pot (Joint A.F G))) (p : ℕ) :=
  let idx:=includeX (G:=G) A.F (boxX y b)
  Lapaz.owes (vene (boxX y b) A.F G) (pinch idx (mold A.pre A.F A.v))⁻¹
    (barbed A.F A.v χ A.T) src (innerPoint A J y z b U) p

theorem cell_columns (A : Mosaic.Issue G) (χ : ChartRatio G) (J : Voice G) (clear : Clear G J)
    (y : ℝ) (z : Positions (Primary A.c G)) (b : Site A.f) {κ d k h C W β : ℝ} (s m p : ℕ)
    (suite : Suite J χ A.F (boxX y b) (boxY y b) (represent (tint G (Exterior.Body 1 A.c) z))
      A.v A.pre (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y) κ d k h (linCash A.F z))
    (solve : Solver (includeX (G:=G) A.F (boxX y b)) (address A.F G ∘ Sum.inr) 0 β C W s (mold A.pre A.F A.v))
    (hβ : 0≤β) (hy : 0≤y) (hsmall : 0≤A.fClock⁻¹ ∧ A.fClock⁻¹≤y)
    (hcost : k+pillow y ≤ 1)
    (U : Config G A.f) (live : U∈hotel A.F (boxX y b) (boxY y b) J
      (represent (tint G (Exterior.Body 1 A.c) z)) (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y))
    (hglobal : ‖bulkPoint A z‖≤y^3) (hlocal : ‖innerPoint A J y z b U‖≤y^3)
    (src : PowerSeries (Pot (Joint A.F G))) (kind : Kind (barbed A.F A.v χ A.T))
    (hbank : ∀ i≤p, Tokew (address A.F G) β s m 0 (PowerSeries.coeff i (barbed A.F A.v χ A.T)) y ∧
        (PowerSeries.coeff i (barbed A.F A.v χ A.T)).totalDegree≤ m)
    (hsrc : ∀ i≤p, Vault (address A.F G) {b} β s m 0 (PowerSeries.coeff i src) y ∧
        (PowerSeries.coeff i src).totalDegree≤ m) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    |Bakery.taste p (bulkColumn A χ z src p) t - Bakery.taste p (innerColumn A χ J y z b U src p) t| ≤
    Real.exp (-β*spotN y) * ((p+1:ℕ)*
      (Spruce.cardK p m C (y*(1+y^3)^(m+1))*(W*C+y*W))) := by
  let exp:=Real.exp (-β*spotN y)
  let l:=address A.F G
  have pos:= (Real.exp_pos (-β*spotN y)).le
  have gap:=Spruce.pitches A.F A.pre A.v (boxX y b) b solve le_rfl hβ (Mosaic.housing A.F b y)
  have move : ∀ i:Joint A.F G, |bulkPoint A z i - innerPoint A J y z b U i|≤exp*(y*W)*Eve β b (l i) := by
    intro i
    cases i with
    | inl i=>
      change |(A.fClock⁻¹•z) i - (A.fClock⁻¹•z) i|≤_
      rw [sub_self,abs_zero]
      exact mul_nonneg (mul_nonneg pos (mul_nonneg hy solve.hsize)) (Real.exp_pos _).le
    | inr i=>
      change |A.fClock⁻¹*bulkCoordinate A z i-A.fClock⁻¹*interiorCoordinate A J y z b U i|≤_
      rw [←mul_sub,abs_mul,abs_of_nonneg hsmall.1,abs_sub_comm]
      have one:=(schur_core_rows A J χ clear y z b suite solve hβ i).1 U live
      change |interiorCoordinate A J y z b U i - bulkCoordinate A z i|≤
        (exp*Eve β b (l (Sum.inr i)))*(W*(k+pillow y)) at one
      apply (mul_le_mul hsmall.2 one (abs_nonneg _) hy).trans
      have reduced : W*(k+pillow y)≤W :=
        (mul_le_mul_of_nonneg_left hcost solve.hsize).trans_eq (mul_one _)
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left reduced (mul_nonneg pos (Real.exp_pos _).le)) hy).trans_eq (by simp only [exp,Eve]; ring)
  have merit := Spruce.joker (Rolling.straight A.F G) (vene (boxX y b) A.F G) kind
    ((solve.bids.submatrix (secureY A.F (boxX y b) G)).inv) solve.bids.inv gap hglobal hlocal
    (mul_nonneg pos (mul_nonneg hy solve.hsize)) move
    (fun i hi=>by simpa only [zero_add] using hbank i hi)
    (fun i hi=>by simpa only [zero_add] using hsrc i hi) ht.1 ht.2
  apply merit.trans_eq
  ring

end YM.Integration.FVA1Physical.Wilson
