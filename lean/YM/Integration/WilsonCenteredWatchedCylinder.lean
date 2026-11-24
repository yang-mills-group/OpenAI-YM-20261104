import YM.Integration.WilsonCenteredWatchedShape
import YM.Integration.WilsonMacroscopicRichWatchPlot

/-! Exact sampling of an original exterior detector on the cell-integrated
near source, over one genuine Wilson field and its original vacuum law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredWatchedCylinder
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonCenteredWatchedShape
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n : ℕ} (d : Fin n → ℕ) (w : ∀j,R.family.label (d j)) (W : Watch R.family)

def tags : Fin (n+W.n) → R.family.book.Token :=
  Fin.append (fun i=>⟨d i,w i⟩) W.q

private theorem node {N p:ℕ} (hj:W.t ≤ N) (j:Fin W.n) :
    ceilSite R.family N p (W.held j.succ)= W.among N p j :=by
  have pos : W.held j.succ = R.family.S.gridPoint W.t (W.x j) :=by
    simp [Watch.held,Watch.table,Extraction.Order.grid,points]
  rw [pos]
  exact WilsonMacroscopicRichWatchPlot.grid W.t N p hj (W.x j)

private theorem read {N p:ℕ} (hj:W.t ≤ N) (r:ℝ) (x:Points n) :
    (rounded R.family N p).read (joint W r x) (tags R d w W) =
      R.family.numeric N p (tags R d w W)
        (Fin.append (site R r (N,p) x) (W.among N p)) :=by
  apply congrArg (R.family.numeric N p (tags R d w W))
  funext k
  refine Fin.addCases (fun i=>?_) (fun j=>?_) k
  · simp only [joint,points,WithLp.ofLp_toLp,Fin.append_left]
    rfl
  · simp only [joint,points,WithLp.ofLp_toLp,Fin.append_right]
    exact node R W hj j

/-- Each exterior link is kept at its actual original reporting image. All
cutoff fine sites of the submitted near test retain their independent lifts. -/
theorem original (φ : Test n) (r : ℝ) {N p:ℕ} (hj:W.t ≤ N) :
    moment (R.family.beta N p) (fun U=>
      cylinder R d (N,p) w (mass R φ r (N,p)) U * W.plot N p U) =
    ∫x,φ x * (rounded R.family N p).read (joint W r x) (tags R d w W) :=by
  let e (u:Sites R (N,p) n) :=
    R.family.numeric N p (tags R d w W) (Fin.append u (W.among N p))
  let prod (u:Sites R (N,p) n) (U:Config G (R.family.side N p)) :=
    ∏j,R.family.O N p (w j) (u j) U
  have full (u:Sites R (N,p) n) : e u = moment (R.family.beta N p) (fun U=>prod u U * W.plot N p U) :=by
    rw [show e u = _ from R.family.num (tags R d w W) (Fin.append u (W.among N p))]
    apply integral_congr_ae
    filter_upwards with U
    change (∏i,R.family.seen (tags R d w W i) (Fin.append u (W.among N p) i) U)=_
    rw [Fin.prod_univ_add]
    simp only [tags,Fin.append_left,Fin.append_right]
    rfl
  have first : moment (R.family.beta N p)
      (fun U=>cylinder R d (N,p) w (mass R φ r (N,p)) U * W.plot N p U)=
      ∑u:Sites R (N,p) n,mass R φ r (N,p) u * e u :=by
    change (∫U,(∑u,mass R φ r (N,p) u * prod u U) * W.plot N p U ∂law G _ (R.family.beta N p))=_
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro u _
      rw [integral_const_mul,full]
      rfl
    · intro u _
      have h : Continuous (fun U=>mass R φ r (N,p) u * (prod u U * W.plot N p U)) :=
        continuous_const.mul ((continuous_finsetProd _ fun j _=>R.family.continuousO N p _ _ _).mul
          (continuous_finsetProd _ fun j _=>R.family.continuousO N p _ _ _))
      exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [first]
  simp_rw [read R d w W hj]
  change _=∫x,φ x * e (site R r (N,p) x)
  have split (x:Points n) : φ x * e (site R r (N,p) x) =
      ∑u,(cell R r (N,p) u).indicator (fun y=>φ y * e u) x :=by
    simp [Set.indicator_apply,cell]
  simp_rw [split]
  rw [integral_finsetSum _ (fun u _=>((φ.continuous.integrable_of_hasCompactSupport
    φ.hasCompactSupport).mul_const (e u)).indicator (measurable_cell R r (N,p) u))]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_indicator (measurable_cell R r (N,p) u),integral_mul_const]
  rfl

end YM.Integration.WilsonCenteredWatchedCylinder
