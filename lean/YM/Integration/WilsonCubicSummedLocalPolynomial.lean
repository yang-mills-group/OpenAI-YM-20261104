import YM.Integration.WilsonCubicLocalPolynomial
import YM.WilsonCoeffUV.Reclosure.Pricing

/-! The rooted Taylor coefficients used in the physical polynomial sum
to the prescribed finite-period cubic, at each rank and each set of legs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonCubicSummedLocalPolynomial
open WilsonCoeffUV
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Power Stationary AnalyticNext.QuarticMatch.Estimate Near
open Work.G05 WilsonCubicLocalPolynomial
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {f : Side} {t k : ℕ} {s a : ℝ}

def orbit (G : Gauge) (f : Side) (l : Signed) : Link G f →L[ℝ] fieldDir G f 1 :=
  (arm G f 1).toContinuousLinearMap.comp (orderTurn l)

def site (A : ℕ → Atom G t) (l : Signed) (p : Site f) : Link G f → ℝ :=
  atend A p ∘ orbit G f l

theorem local_sum (A : ℕ → Atom G t) (hs : 0<s) (cash : SumBudget (fun i => (A i).budget s) a)
    (l : Signed) (p : Site f) (x : Fin k → Woods G f) :
    HasSum (fun i => rye (reader A (l,p,i)) k x) (rye (site A l p) k x) := by
  let L := orbit G f l
  let P := Blue.pebble ∘ x
  have budget := cash.2.1.mul_left (((2:ℝ)^k*gratuity G (down s k) k)^t)
  have h : HasSum (fun i => iteratedFDeriv ℝ k (Cargo.effect (A i) p) 0)
      (iteratedFDeriv ℝ k (atend A p) 0) :=
    honorable (fun i => Cargo.effective ..) budget (m:=k) (Metric.ball (0:fieldDir G f 1) 1)
      isOpen_ball (convex_ball _ _).isPreconnected
      (fun i y hy j hj => neighbors y (le_of_lt (by simpa using hy)) hs _ _ hj _) (by simp) k le_rfl
  have term (i : ℕ) : reader A (l,p,i) = Cargo.effect (A i) p ∘ L :=
    issued A (l,p,i)
  have a0 : rye (site A l p) k x = (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k (atend A p) 0 (L ∘ P) := by
    rw [rye,show site A l p=atend A p ∘ L from rfl,wired L (Village.atend_rate A hs cash p (L 0)).analyticAt,map_zero]
  have each (i : ℕ) : rye (reader A (l,p,i)) k x =
      (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k (Cargo.effect (A i) p) 0 (L ∘ P) := by
    rw [rye,term,wired L ((Cargo.effective (A i) p).contDiffAt.analyticAt (x:=L 0)),map_zero]
  simp_rw [each,a0]
  exact ((ContinuousMultilinearMap.apply ℝ _ ℝ (L ∘ P)).hasSum h).const_smul _

private theorem sum_green {ι : Type} [Fintype ι] (z : ι → Link G f → ℝ)
    (good : ∀ i, Green (z i)) : Green (∑ i,z i) := by
  rw [show (∑ i,z i) = (fun u => ∑ i,z i u) from funext fun _ => Finset.sum_apply ..]
  exact ContDiffAt.sum fun i _ => good i

private theorem add_rows {ι : Type} [Fintype ι] (z : ι → Link G f → ℝ) (good : ∀ i, Green (z i)) (k : ℕ) :
    rye (∑ i,z i) k = ∑ i,rye (z i) k := by
  have all := sum_green z good
  have h := jet_sum (U:=Woods G f) Finset.univ z (fun i _ => good i)
  apply unique_kernel (rye_sym all k) (Blue.Smooth.sum (fun i _ => rye_sym (good i) k))
  rw [← jet_apply,h,map_sum,map_sum]
  simp_rw [jet_apply]

private theorem written (A : ℕ → Atom G 3) :
    turnSeries A (m:=f) = (Fintype.card Signed : ℝ)⁻¹ • (∑ l : Signed, ∑ p : Site f, site A l p) := by
  funext u
  rw [turns_frame]
  simp only [Patch.average,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  exact congrArg ((Fintype.card Signed : ℝ)⁻¹ * ·) (Finset.sum_congr rfl fun _ _ => rfl)

theorem original (A : ℕ → Atom G 3) (hs : 0<s) (cash : SumBudget (fun i => (A i).budget s) a)
    (k : ℕ) (x : Fin k → Woods G f) :
    Mosaic.surf (WilsonCubicPrintedTensor.source A) f (k-2) k x =
      Patch.average fun l : Signed => ∑ p : Site f, ∑' i, rye (reader A (l,p,i)) k x := by
  have each (l : Signed) (p : Site f) : Green (site A l p) :=
    (Village.atend_rate A hs cash p _).comp _ (orbit G f l).contDiff.contDiffAt
  have all (l : Signed) := sum_green _ (each l)
  have whole := sum_green _ all
  rw [WilsonCubicPrintedTensor.rank A hs cash,written,rye_mu _ _ whole,add_rows _ all]
  simp only [Patch.average,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  apply congrArg ((Fintype.card Signed : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro l _
  rw [add_rows _ (each l),Finset.sum_apply]
  exact Finset.sum_congr rfl fun p _ => (local_sum A hs cash l p x).tsum_eq.symm

end YM.Integration.WilsonCubicSummedLocalPolynomial
