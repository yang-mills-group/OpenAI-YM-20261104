import YM.Integration.WilsonThermometerOriginalForestLetters
import YM.Comparison.RG02.Cumulants.Parents

/-! The first two coefficients of an entire finite Wick table, including its quiet divisor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalForestTable
open Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Order Primitives.GCC.Anchor Next.SectorChange
open scoped Classical BigOperators ContDiff

private def Matches {A:Type*} [CommSemiring A] (r:ℕ) (u v:PowerSeries A) : Prop :=
  ∀ n≤r, PowerSeries.coeff n u=PowerSeries.coeff n v

private theorem products {A:Type*} [CommSemiring A] {r:ℕ} {u v x y:PowerSeries A}
    (h:Matches r u v) (k:Matches r x y) : Matches r (u*x) (v*y) := by
  intro n hn
  rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  have pair:a+b=n := by simpa using hab
  rw [h a (by omega),k b (by omega)]

private theorem powers {A:Type*} [CommSemiring A] {r:ℕ} {u v:PowerSeries A}
    (h:Matches r u v) (i:ℕ) : Matches r (u^i) (v^i) := by
  induction i with
  | zero => simp only [pow_zero]; exact fun _ _=>rfl
  | succ i ih => simpa only [pow_succ] using products ih h

variable {G:Gauge} {c f:Side} {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {S:StepData c f} {clip:Clip} {P:PathData G} {O:ChartRatio G}

private theorem marks {r:ℕ} {u v:PTable R} (h:Matches r u v) : Matches r (markExp u) (markExp v) := by
  intro n hn
  simp only [markExp,map_sum,PowerSeries.coeff_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [powers h i n hn]

private theorem sourceRows (F:Forest S.ratio) (K:Bulk.Kernel S clip P O) (t:S.Choices)
    (X Y:Bulk.Colors R G f) (r:ℕ) (geo:Bulk.geometric K F t X=Bulk.geometric K F t Y)
    (heads:∀ (s:Hot R) j, j≤r → ∀ u:Bulk.Joint S F (G:=G),
      jet (Bulk.markFn S F X s) (X.power s+j) u=jet (Bulk.markFn S F Y s) (Y.power s+j) u)
    (s:R.Mode) (j:ℕ) (hj:j≤r) (u:Bulk.Joint S F (G:=G)) :
    rows (expansions X.power (Bulk.markFn S F X) (Bulk.geometric K F t X)) s j u=
      rows (expansions Y.power (Bulk.markFn S F Y) (Bulk.geometric K F t Y)) s j u := by
  have hc:Matches r (curve X.power (Bulk.markFn S F X) u) (curve Y.power (Bulk.markFn S F Y) u) := by
    intro n hn
    simp only [curve,PowerSeries.coeff_mk]
    exact congrArg (lit R) (funext fun b=>heads b n hn u)
  unfold rows expansions
  rw [geo]
  apply congrArg (fun H:Poly R=>H.part s)
  exact products (fun _ _=>rfl) (marks hc) j hj

private theorem view (F:Forest S.ratio) (K:Bulk.Kernel S clip P O) (t:S.Choices)
    (X:Bulk.Colors R G f) (p:ℕ) (angle:fieldDir G c 1) (s:R.Mode) (j:ℕ) (hp:j≤p) :
    (observe R p (Bulk.Fk K F t X angle p) j).part s=
       ∫ z, rows (expansions X.power (Bulk.markFn S F X) (Bulk.geometric K F t X)) s j
         (Bulk.translated K F angle z) ∂Gaussian.cloud (K.covariance F t) := by
  have h:=observed (x:=Bulk.Fk K F t X angle p) s hp
  rw [Bulk.table,picked p hp] at h
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.factorial_pos j).ne' : (j.factorial:ℂ)≠0) h

/-- All subwords, at every true held field, in the original tag-dependent Gaussian marginal. -/
theorem original (F:Forest S.ratio) (K:Bulk.Kernel S clip P O) (t:S.Choices)
    (X Y:Bulk.Colors R G f) (r p:ℕ) (angle:fieldDir G c 1)
    (geo:Bulk.geometric K F t X=Bulk.geometric K F t Y)
    (heads:∀ (s:Hot R) j, j≤r → ∀ u:Bulk.Joint S F (G:=G),
      jet (Bulk.markFn S F X s) (X.power s+j) u=jet (Bulk.markFn S F Y s) (Y.power s+j) u)
    (j:ℕ) (hj:j≤r) (hp:j≤p) :
    observe R p (Bulk.Fk K F t X angle p) j=observe R p (Bulk.Fk K F t Y angle p) j := by
  ext1 s
  rw [view F K t X p angle s j hp,view F K t Y p angle s j hp]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with z
  exact sourceRows F K t X Y r geo heads s j hj _

theorem ground (F:Forest S.ratio) (K:Bulk.Kernel S clip P O) (t:S.Choices)
    (X Y:Bulk.Colors R G f) (p:ℕ) (angle:fieldDir G c 1)
    (geo:Bulk.geometric K F t X=Bulk.geometric K F t Y)
    (heads:∀ (s:Hot R) j, j≤1 → ∀ u:Bulk.Joint S F (G:=G),
      jet (Bulk.markFn S F X s) (X.power s+j) u=jet (Bulk.markFn S F Y s) (Y.power s+j) u) :
    First.buc (logMarked (Bulk.Fk K F t X angle p))=
      First.buc (logMarked (Bulk.Fk K F t Y angle p)) := by
  rw [Cumulants.orphan (Bulk.fk_sym ..) (Bulk.fk_unit ..),Cumulants.orphan (Bulk.fk_sym ..) (Bulk.fk_unit ..)]
  exact congrArg Extra.Trajectories.connected
    (original F K t X Y 1 p angle geo heads 0 (by decide) (Nat.zero_le _))

/-- The complete signed first connected coefficient, with the actual quiet normalization. -/
theorem connected (F:Forest S.ratio) (K:Bulk.Kernel S clip P O) (t:S.Choices)
    (X Y:Bulk.Colors R G f) (p:ℕ) (hp:0<p) (angle:fieldDir G c 1)
    (geo:Bulk.geometric K F t X=Bulk.geometric K F t Y)
    (heads:∀ (s:Hot R) j, j≤1 → ∀ u:Bulk.Joint S F (G:=G),
      jet (Bulk.markFn S F X s) (X.power s+j) u=jet (Bulk.markFn S F Y s) (Y.power s+j) u) :
    Order.First.ind (logMarked (Bulk.Fk K F t X angle p))=
      Order.First.ind (logMarked (Bulk.Fk K F t Y angle p)) := by
  have pair:=original F K t X Y 1 p angle geo heads
  rw [First.first_log hp (Bulk.fk_sym ..) (Bulk.fk_unit ..),
    First.first_log hp (Bulk.fk_sym ..) (Bulk.fk_unit ..)]
  change _*inverseMass (observe R p _ 0)-_=_*inverseMass (observe R p _ 0)-_
  rw [pair 0 (by decide) (Nat.zero_le p)]
  change observe R p _ 1*_-Poly.bead R ((observe R p _ 1).part R.quiet)=_
  rw [pair 1 le_rfl hp]

end YM.Integration.WilsonThermometerOriginalForestTable
