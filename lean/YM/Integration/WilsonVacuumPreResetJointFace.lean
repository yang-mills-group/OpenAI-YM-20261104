import YM.Integration.WilsonVacuumPreResetJointSite
import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceRay

/-! The direct Wilson part of the measured kinetic coefficient on each
original oriented four-link plaquette. The trace smoothness and its real
joint Taylor cost do not depend on the size of the torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointFace
open Stationary Function Filter Finset Lattice RG Wilson Tree Pressure Gauge Precision
open Push Push.Uniform Push.AbsoluteSums ConnectedActivityE6 Coat Control Blaze
open AnalyticNext.QuarticMatch.Estimate RG01.Sounder Logfee Work.G05
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw WilsonVacuumPreResetJointSite
open OriginalMarkedRunAction
open private increment_link from YM.Integration.WilsonVacuumPreResetJointTicket
open private collected from YM.Integration.WilsonVacuumPreResetJointSite
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def face (s : Signed) (x : Site f) (a : PlaqAxes) (U : Config G f) : ℝ :=
  G.price (faceValue (pull s 0 U) (x,a))

def cost (G : Gauge) (j : ℕ) (C : ℝ) : ℝ :=
  1+tracePrice G*travelCost G j 4 C

private theorem observed (j : ℕ) (U : E → Config G f) (y : E) {C : ℝ}
    (due : ∀ i, Allows j (fun w => G.mat (U w i)) y C) (s : Signed) (x : Site f) (a : PlaqAxes) :
    Brush j (cost G j C) 1 (face s x a ∘ U) y := by
  have h (i : Bond f) : Allows j (fun w => G.mat (pull s 0 (U w) i)) y C := by
    let d := (posDir i.2).rotate s
    let q := affine s (0 : Site f) i.1
    have path := due (d.used q)
    unfold pull Lattice.Step.read; split
    · exact path.inverse (f:=fun w => U w _)
    exact path
  have word := travel_jets (U:=fun w => pull s 0 (U w)) h x
    (w:=square a.val.1 a.val.2) (le_refl 4)
  have scalar := word.linear (normalizedTrace G) (K:=tracePrice G)
    (ContinuousLinearMap.opNorm_le_bound _ (by unfold tracePrice; positivity)
      (fun M => trace_bound G M))
  have pay : Brush j (tracePrice G*travelCost G j 4 C) 1
      (fun w => normalizedTrace G (G.mat (travel (pull s 0 (U w)) x (square a.val.1 a.val.2)))) y := by
    exact Brush.offer.mpr ⟨scalar.analytic.of_le le_top, scalar.norm_le⟩
  have total := (Brush.certified (k:=j) (x:=y) zero_le_one (1:ℝ)).separating pay
  rw [norm_one] at total
  exact total.shimmy (Filter.Eventually.of_forall fun w => trace_price _ _ _)

def charge (G : Gauge) (j r : ℕ) (t : ℝ) : ℝ :=
  let h := j+(r+2)+1
  j.factorial*cost G h (linkFee G h)*(1+((1+1)*1):ℝ)^j*t^(r+3)

def paper (P : Finset (Bond c)) (X : Coat T F) (d : ℕ) (x : Site f) (v : Arguments G c f) : ℝ :=
  Patch.average fun s : Signed => ∑ a : PlaqAxes, developed P X d (face s x a) v

theorem atom (P : Finset (Bond c)) (X : Coat T F) (s : Signed) (x : Site f) (a : PlaqAxes)
    (r j : ℕ) {y : E} {z : E → Arguments G c f} (u : ℝ)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    Brush j (|u| * charge G j r t) 1 (fun w => u *
      (face s x a (field P X (z w)) - developed P X (r+2) (face s x a) (z w))) y := by
  let d := r+2
  let h := j+d+1
  have smooth := (observed d (increment (field P X 0)) 0
    (increment_link (field P X 0) d 0) s x a).smooth
  have grade := composition P X (face s x a) d smooth
  have localDue (v : Arguments G c f) (_ : ‖v‖ ≤ t) :=
    observed h (field P X) v (links P X h v) s x a
  have estimate := (LocalTaylorR2.Mesh.priced (d:=d) ht ht' localDue read).smul u
  rw [grade] at estimate
  exact estimate

theorem measured (P : Finset (Bond c)) (X : Coat T F) (x : Site f) (r j : ℕ)
    {y : E} {z : E → Arguments G c f} (u : ℝ)
    {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    Brush j ((Fintype.card PlaqAxes : ℝ) * (|u| * charge G j r t)) 1
      (fun w => u*(facePriceAt x (field P X (z w)) - paper P X (r+2) x (z w))) y := by
  have h (s : Signed) := Brush.spree (univ : Finset PlaqAxes) _
    (fun _ => |u| * charge G j r t) zero_le_one
    (fun a _ => atom P X s x a r j u ht ht' read)
  have all := collected _ h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at all
  apply all.shimmy (Filter.Eventually.of_forall fun w => ?_)
  simp only [facePriceAt, paper, Patch.average, face, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end YM.Integration.WilsonVacuumPreResetJointFace
