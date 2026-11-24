import YM.Integration.WilsonMatrixTicketLanesConnectedColumns
import YM.Integration.WilsonMatrixTicketLanesConnectedSampling
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

/-! Numerical spatial decay with the original atRef frame costs of both submitted fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedWeighted
open Function Filter Finset Real Lattice Gauge RG Tree Wilson Source Marker Extraction Spec RG12 RG17
open PhysicalNext.Repeat.Legato FullVolume Extraction.Order RGComparison.Core16 RGComparison.Core16.Spool
open WilsonInvariantActionSeparatedCells Table Climb Trace.Pilot Next.UVStress Pert.Asymptotics
open WilsonMatrixTicketLanesReflectedGauge WilsonMatrixTicketLanesConnectedBudget WilsonMatrixTicketLanesConnectedForecast
open WilsonMatrixTicketLanesConnectedColumns WilsonMatrixTicketLanesReportedOneBlock
open private single from YM.Integration.WilsonMatrixTicketLanesReportedPlatedBank
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)

private theorem total {I J : Type} [Fintype I] [Fintype J] (c : I→ℂ) (d : J→ℂ) (v : I→J→ℝ) {a : ℝ}
    (small : ∀i j,|v i j| ≤ a) : ‖∑i,∑j,(c i*d j)*(v i j:ℂ)‖ ≤ (∑i,‖c i‖)*(∑j,‖d j‖)*a:=by
  calc
    _ ≤ ∑i,∑j,‖(c i*d j)*(v i j:ℂ)‖:= (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _=>norm_sum_le _ _)
    _ ≤ ∑i,∑j,‖c i‖*(‖d j‖*a):=Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun j _=>by
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (small i j) (norm_nonneg _)) (norm_nonneg _)
    _ = _:=by simp_rw [←Finset.mul_sum,←Finset.sum_mul];ring

private theorem atDate (e : Request G) (ε : ℝ) (m : ℝ→ℕ) (φ : Test 2) (r : ℝ)
    (bill : WilsonMatrixTicketLanesConnectedSampling.Row R e ε m φ r) (b k : ℕ) (date : k=b+1) (filed : k=m r)
    (hr : 0<r) (N p : ℕ) (future : k ≤ N) (x : Fin 2→Site (R.family.side N p))
    (live : WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0) (T : Forest (step R p date).ratio)
    (actual : Bid.Larger (G:=G) (step R p date)) (u : Directions G (R.family.side b p)) (pin : ∀i,‖u i‖ ≤ (e.2.2:ℝ)+1) :
    let o:=fun i=>(R.family.S.toDepth future p).parent (x i)
    |measured (step R p date) u R (row e) (col e) (left e) (right e) (fun _=>o 0) (fun _=>o 1)
      (regulatorRun R.family N p k)| ≤ ε*(regulatorRun R.family N p k)^e.2.1:=by
  subst k;exact bill b filed hr N p future x live T actual u pin

variable {f : Extraction.Order} {S : Table R.family.book} (F : Spec.Final R.family f S) (L : RG17.Layout F)

def amount (d : ℕ) (r : ℝ) (w : R.family.label d) : ℝ := (2:ℝ)^d * mass R.family d (L.shift d r w)

/-- Every original matrix entry shares one before-radius bound. The emitted complex labels and their fees may still depend on the actual radius. -/
theorem plated (simple : G.Simple) (paid : Paid G R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (large : 17 ≤ B) (level : L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    (d h q cap : ℕ) (φ : Test 2) (ε : ℝ) (positive : 0<ε) : ∀ᶠ r in trail,
    ∀ b (date : L.level r=b+1) (hr : 0<r) (w : R.family.label d) (v : R.family.label h) N p (future : L.level r ≤ N)
      (x : Fin 2→Site (R.family.side N p)),WilsonExternalMeshMass.charge R.family (dilate hr φ) x≠0 →
      let o:=fun i=>(R.family.S.toDepth future p).parent (x i)
      ∀ (_T : Forest (step R p date).ratio),Bid.Larger (G:=G) (step R p date) →
      ∀(u : Directions G (R.family.side b p)), (∀i,‖u i‖ ≤ (cap:ℝ)+1) →
      ‖joint R F L r d h w v b N p date u (o 0) (o 1)-WilsonMatrixTicketLanesConnectedColumns.single R F L r d w b N p date u (o 0)*
        WilsonMatrixTicketLanesConnectedColumns.single R F L r h v b N p date u (o 1)‖ ≤
        amount R F L d r w*amount R F L h r v*(ε*(regulatorRun R.family N p (L.level r))^q):=by
  let code (i : BasisIndex R d) (j : BasisIndex R h) : Request G:=((⟨d,i⟩,⟨h,j⟩),(q,cap))
  let m:=WilsonMeasuredWindow.stop R.family.path.levels simple B
  have issued : ∀ᶠ r in trail,∀ i j,WilsonMatrixTicketLanesConnectedSampling.Row R (code i j) ε m φ r :=
    eventually_all.mpr fun i=>eventually_all.mpr fun j=>WilsonMatrixTicketLanesConnectedSampling.original R simple paid pace (code i j) ε positive large φ
  have grows : Tendsto L.level trail atTop:=by rw [level];exact WilsonMeasuredWindow.stop_tendsto _ simple B (by omega)
  filter_upwards [issued,grows.eventually_ge_atTop (R.family.ref d),grows.eventually_ge_atTop (R.family.ref h)]
    with r reports age other b date hr w v N p future x live o T actual u pin
  have eps : 0 ≤ ε*(regulatorRun R.family N p (L.level r))^q := mul_nonneg positive.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  rw [exact_sum R F L r d h w v b N p date future age other u (o 0) (o 1)]
  apply (total (a:=ε*(regulatorRun R.family N p (L.level r))^q) (weights R F L r d w N p) (weights R F L r h v N p) _
    (fun i j=>by simpa only [code,row,col,left,right] using atDate R (code i j) ε m φ r (reports i j) b (L.level r) date (congrFun level r) hr N p future x live T actual u pin)).trans
  apply mul_le_mul_of_nonneg_right _ eps
  have l : (∑i,‖weights R F L r d w N p i‖) ≤ amount R F L d r w:=single R F L d r w N p future
  have h' : (∑j,‖weights R F L r h v N p j‖) ≤ amount R F L h r v:=single R F L h r v N p future
  exact mul_le_mul l h' (Finset.sum_nonneg fun _ _=>norm_nonneg _) ((Finset.sum_nonneg fun _ _=>norm_nonneg _).trans l)

end YM.Integration.WilsonMatrixTicketLanesConnectedWeighted
