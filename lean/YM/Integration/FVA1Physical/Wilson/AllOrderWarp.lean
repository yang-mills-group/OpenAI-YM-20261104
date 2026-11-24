import YM.Integration.FVA1Physical.Wilson.TwoLinkChart
import YM.Integration.FVA1Physical.Wilson.ClockSliceTensor
import YM.Integration.FVA1Physical.Wilson.PacketGrade

/-! Full operator-norm Taylor comparison for the nonlinear fine chart.
The ordinary source is tested only on the physical one-clock unit ball.
The forest and the period do not enter the chart constants. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG YM.Wilson Exterior Tree Comparison.RG02 Assembly
open scoped Topology Classical ContDiff BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio)
local notation "E" => Bulk.Joint S F (G:=G)
local notation "X" => ℝ × fieldDir G f 1

def ordinaryTensorRent (j:ℕ):ℝ:=(j.factorial:ℝ)*(2*(Contacts.Loom.poly_rent j).choose*clockRent j)

def chartTensorRent (G:Gauge) (n:ℕ) (cost:ℕ→ℝ):ℝ:=
  ∑ c:OrderedFinpartition n,cost c.length*∏ i:Fin c.length,linkChartCost G (c.partSize i)

private theorem polar_bill {Y:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a b:ℝ×Y→ℂ} (ha:ContDiffAt ℝ ω a 0) (hb:ContDiffAt ℝ ω b 0) (j:ℕ) {δ:ℝ}
    (seen:∀u:Y,‖u‖≤1→‖jet a j (1,u)-jet b j (1,u)‖≤δ):
    ‖iteratedFDeriv ℝ j (a-b) 0‖ ≤ ordinaryTensorRent j*δ:=by
  have eq:iteratedFDeriv ℝ j (a-b) 0=(j.factorial:ℝ) • (Tensor.coeff a j 0-Tensor.coeff b j 0):=by
    rw [Tensor.coeff,Tensor.coeff,←smul_sub,smul_smul,mul_inv_cancel₀ (by positivity : (j.factorial:ℝ)≠0),one_smul]
    rw [iteratedFDeriv_sub_apply (ha.of_le le_top) (hb.of_le le_top)]
  rw [eq,norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have cc:=clock_slice_tensor ha hb j seen
  calc _ ≤ (j.factorial:ℝ)*(2*(Contacts.Loom.poly_rent j).choose*(clockRent j*δ)) :=
        mul_le_mul_of_nonneg_left cc (Nat.cast_nonneg _)
       _ = ordinaryTensorRent j*δ:=by unfold ordinaryTensorRent;ring

private theorem chart_norm (a:X→ℂ) (smooth:ContDiffAt ℝ ω a 0) (n:ℕ) (cost:ℕ→ℝ)
    (paid:∀j≤n, ‖iteratedFDeriv ℝ j a 0‖≤cost j):
    ‖iteratedFDeriv ℝ n (a ∘ fineLogChart F) 0‖≤chartTensorRent G n cost:=by
  let L:=fineLogChart F (G:=G)
  have zero:L 0=0:=congrArg (fun q:Work.F03.Logs G c f=>((0:ℝ),q.2)) (Work.F03.inclusion_zero F)
  have sl:ContDiffAt ℝ ω L 0:=contDiffAt_fst.prodMk
    ((Work.F03.inclusion_smooth F).snd.comp (f:=Prod.snd) (0:E) contDiffAt_snd)
  have atL:ContDiffAt ℝ ω a (L 0):=zero.symm ▸ smooth
  let b(j:ℕ):=iteratedFDeriv ℝ j a 0
  let l(j:ℕ):=iteratedFDeriv ℝ j L 0
  have exactRows:iteratedFDeriv ℝ n (a ∘ L) 0=
      ∑ k:OrderedFinpartition n,k.compAlongOrderedFinpartition (b k.length) (fun i=>l (k.partSize i)):=by
    rw [iteratedFDeriv_comp atL sl le_top,FormalMultilinearSeries.taylorComp,zero]
    rfl
  change ‖iteratedFDeriv ℝ n (a ∘ L) 0‖≤_
  rw [exactRows]
  apply (norm_sum_le ..).trans
  refine Finset.sum_le_sum fun k _=>?_
  apply (k.norm_compAlongOrderedFinpartition_le (b k.length) (fun i=>l (k.partSize i))).trans
  exact mul_le_mul (paid k.length k.length_le)
    (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>fineChart_uniform F (k.partSize i)))
    (prod_nonneg fun _ _=>norm_nonneg _) ((norm_nonneg _).trans (paid k.length k.length_le))

/-- Multilinear tensor in arbitrary independent directions at the actual
nonlinear gauge-chart origin. Grade below the insertion degree costs zero.
No matching of lower marked coefficients is assumed. -/
theorem all_orders_chart (U V:ℝ → Config G f → ℂ) {k:ℕ}
    (hu:GradeAt k (Bulk.projected U)) (hv:GradeAt k (Bulk.projected V)) (p:ℕ) (δ:ℕ→ℝ)
    (seen:∀s≤p,∀u:fieldDir G f 1,‖u‖≤1→
      ‖jet (Bulk.projected U) (k+s) (1,u)-jet (Bulk.projected V) (k+s) (1,u)‖≤δ s):
    ‖iteratedFDeriv ℝ (k+p) (Bulk.posed S F U-Bulk.posed S F V) 0‖≤
      chartTensorRent G (k+p) (fun j=> if k≤j then ordinaryTensorRent j*δ (j-k) else 0):=by
  let a:=Bulk.projected U
  let b:=Bulk.projected V
  let L:=fineLogChart F (G:=G)
  have eq:(Bulk.posed S F U-Bulk.posed S F V)=ᶠ[𝓝 0] (a-b) ∘ L:=by
    filter_upwards [(continuous_snd.tendsto (0:E)).eventually (Work.F03.inclusion_works F)] with u h
    exact congrArg (fun z=>U u.1 z-V u.1 z) h.symm
  rw [(eq.iteratedFDeriv ℝ (k+p)).eq_of_nhds]
  apply chart_norm F (a-b) (hu.smooth.sub hv.smooth)
  intro j hj
  split
  next h =>
    have index:k+(j-k)=j:=Nat.add_sub_of_le h
    apply polar_bill hu.smooth hv.smooth
    simpa only [index] using seen (j-k) (by omega)
  next h =>
    rw [(hu.sub hv).vanish j (Nat.lt_of_not_ge h), norm_zero]

end YM.Integration.FVA1Physical.Wilson
