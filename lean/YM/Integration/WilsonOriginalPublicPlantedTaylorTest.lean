import YM.Integration.WilsonOriginalPublicPlantedTaylorTail
import YM.Integration.WilsonPositionProgramTrialCellVariation

/-! The signed common-center test of the complete normalized public product on the
ordered inversion board. Only nodes with a nonzero original smear incur a fare. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedTaylorTest
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Rose XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries
open WilsonPositionProgramPublicDirectoryCoin (drawValue)
open WilsonOriginalPublicPlantedTaylorTail (value)
open scoped Topology BigOperators Classical
variable {n:ℕ}

private theorem touch (M:Mesh)(φ:Test n)(z:pack n)(hit:M.smear z φ≠0):
    ∃c∈M.Box,M.rel z c∈tsupport φ:=by
  by_contra! empty
  apply hit
  change M.vol⁻¹ • (∫c in M.Box,M.termView φ z c)=0
  have gone(c:Four ℝ)(inside:c∈M.Box):M.termView φ z c=0:=
    image_eq_zero_of_notMem_tsupport (f:=φ) (empty c inside)
  rw [setIntegral_eq_zero_of_forall_eq_zero gone,smul_zero]

theorem integrated (M:Mesh)(φ:Test n)(X Y:Sample n→ℂ)(e:ℝ)
    (heard:∀z:pack n,∀c∈M.Box,M.rel z c∈tsupport φ →
      ‖X ⟨M,z,0⟩-Y ⟨M,z,0⟩‖≤e):
    ‖Deposit M X φ-Deposit M Y φ‖≤WilsonPositionProgramTrialCellVariation.mass M φ*e:=by
  unfold Deposit WilsonPositionProgramTrialCellVariation.mass
  rw [←mul_sub,←sum_sub_distrib,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg M.positive.le,
    mul_assoc,Finset.sum_mul]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg M.positive.le _)
  apply (norm_sum_le ..).trans (sum_le_sum _)
  intro z _
  rw [←mul_sub,norm_mul]
  by_cases unused:M.smear (M.back z) φ=0
  · simp [unused]
  obtain ⟨c,hc,inside⟩:=touch M φ _ unused
  exact mul_le_mul_of_nonneg_left (heard _ c hc inside) (norm_nonneg _)

variable {G:Gauge}(Z:WilsonPrescription G){sg:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z sg M T dial){d:ℕ}(β:Local.Physical.Deck G)
    {K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n)
    (l:Filter ℝ){t:ℝ→ℝ}(pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))

def tested (v:Tags G d n)(j q:ℕ)(φ:Test n)(u:ℝ):ℂ:=
  Deposit (Z.run.step j) (fun s=>value Z v β j q s u) φ

theorem printed (v:Tags G d n){j B:ℕ}(P:Handoff.Directory Z j B)(q:ℕ)
    (cap:Handoff.Directory.budget G n d+q≤B)(φ:Test n)(u:ℝ):
    tested Z β v j q φ u=∑k∈range (q+1),WilsonPositionRawEpoch.row Z P d φ v k*(u:ℂ)^k:=by
  let m:=Z.run.step j
  rw [WilsonPositionOriginalEpochQuadrature.whole]
  unfold tested Deposit
  apply congrArg (fun b:ℂ=>(m.spacing:ℂ)^(4*n)*b)
  apply sum_congr rfl
  intro z _
  exact congrArg (fun b:ℂ=>m.smear (m.back z) φ*b)
    (show value Z v β j q ⟨m,m.back z,0⟩ u=drawValue Z v q P u (m.back z) from
      (WilsonOriginalPublicPlantedPivotFields.drawn β Z P ⟨m,m.back z,0⟩ v rfl q cap u).symm)

include H compact apart pos small in
theorem original (v:Tags G d n)(J Q:ℕ)(order:J≤Q)(D:ℕ)(C:ℝ){δ:ℝ}(price:0<δ):
    ∃i₀:ℕ,∀ᶠ r in l,∀i≥i₀,(i:ℝ)≤C*(-Real.log (t r))^D →
      ∀{B}(_P:Handoff.Directory Z i B),Handoff.Directory.budget G n d+Q≤B →
      ∀φ:Test n,tsupport φ⊆K → ∀u:ℝ,|u|≤8*t r →
        ‖tested Z β v i Q φ u-tested Z β v i J φ u‖≤
          WilsonPositionProgramTrialCellVariation.mass (Z.run.step i) φ*(δ*(t r)^J):=by
  obtain ⟨i₀,funded⟩:=WilsonOriginalPublicPlantedTaylorTail.directory Z H v compact apart l pos small J Q order D C price
  refine ⟨i₀,?_⟩
  filter_upwards [funded] with r quotes
  intro i late short B P cap φ housing u charge
  refine integrated (Z.run.step i) φ (fun s=>value Z v β i Q s u) (fun s=>value Z v β i J s u) (δ*(t r)^J) ?_
  intro z c inside located
  let s:Sample n:=⟨Z.run.step i,z,c⟩
  have atZero (q:ℕ)(budget:Handoff.Directory.budget G n d+q≤B):
      value Z v β i q ⟨Z.run.step i,z,0⟩ u=drawValue Z v q P u z:=
    (WilsonOriginalPublicPlantedPivotFields.drawn β Z P ⟨Z.run.step i,z,0⟩ v rfl q budget u).symm
  rw [atZero Q cap,atZero J (by omega)]
  exact quotes i late short P cap s rfl inside (housing located) u charge

end YM.Integration.WilsonOriginalPublicPlantedTaylorTest
