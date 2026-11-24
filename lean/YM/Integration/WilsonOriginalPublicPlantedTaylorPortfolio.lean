import YM.Integration.WilsonOriginalPublicPlantedTaylorFees
import YM.Integration.WilsonPositionProgramPublicDirectoryTensor

/-! Actual finite field portfolios in the normalized public directory, including lower
and unit slots. Their high-order bill is the product of the individual basis doses. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicPlantedTaylorPortfolio
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Rose XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Menus MS.Theater PowerSeries
open WilsonOriginalPublicPlantedTaylorTail (value)
open WilsonOriginalPublicPlantedTaylorTest (tested)
open WilsonOriginalPublicPlantedTaylorFees (wage bill)
open WilsonPositionProgramPublicDirectoryTensor (filed)
open WilsonPositionProgramPublicDirectoryCoin (drawValue)
open scoped Topology BigOperators Classical
variable {n:ℕ}

private theorem add {I:Type}[Fintype I](M:Mesh)(φ:Test n)(w:I→ℂ)(X:I→Sample n→ℂ)(F:Sample n→ℂ)
    (rows:∀z:pack n,F ⟨M,z,0⟩=∑a,w a*X a ⟨M,z,0⟩):
    Deposit M F φ=∑a,w a*Deposit M (X a) φ:=by
  unfold Deposit
  simp_rw [rows]
  simp only [Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro z _
  ring

variable {G:Gauge}(Z:WilsonPrescription G){sg:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{T:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z sg M T dial)(β:Local.Physical.Deck G){d:ℕ}
local notation "Γ" => Glyph β d
local notation "axis" => Theater.Daylight β d

theorem expands (v:Tags G d n):filed d β (fun i=>(Theater.Daylight β d).repr (v i))=v:=by
  funext i
  exact (Theater.Daylight β d).sum_repr (v i)

theorem doses (w:Fin n→Γ→ℂ)(m:Mesh)(φ:Test n):
    wage m (fun a:Fin n→Γ=>∏i,w i (a i)) (fun _=>φ)=
      (∏i,∑b,‖w i b‖)*WilsonPositionProgramTrialCellVariation.mass m φ:=by
  unfold wage
  rw [←sum_mul,Fintype.prod_sum]
  simp only [norm_prod]

theorem printed {j B:ℕ}(P:Handoff.Directory Z j B)(q:ℕ)
    (cap:Handoff.Directory.budget G n d+q≤B)(φ:Test n)(u:ℝ)(w:Fin n→Γ→ℂ):
    tested Z β (filed d β w) j q φ u =
      bill Z β (fun (a:Fin n→Γ) i=>axis (a i)) j q (fun a=>∏i,w i (a i)) (fun _=>φ) u:=by
  refine add (Z.run.step j) φ (fun a:Fin n→Γ=>∏i,w i (a i))
    (fun a s=>value Z (fun i=>axis (a i)) β j q s u) (fun s=>value Z (filed d β w) β j q s u) ?_
  intro z
  let s:Sample n:=⟨Z.run.step j,z,0⟩
  have each(v:Tags G d n):value Z v β j q s u=drawValue Z v q P u z:=
    (WilsonOriginalPublicPlantedPivotFields.drawn β Z P s v rfl q cap u).symm
  calc
    _=drawValue Z (filed d β w) q P u z:=each _
    _=∑a:Fin n→Γ,(∏i,w i (a i))*drawValue Z (fun i=>axis (a i)) q P u z:=
      WilsonPositionProgramPublicDirectoryTensor.original P d z β q u w
    _=∑a:Fin n→Γ,(∏i,w i (a i))*value Z (fun i=>axis (a i)) β j q s u:=by simp_rw [each]

variable {K:Set (Points n)}(compact:IsCompact K)(apart:K⊆conf n)
    (l:Filter ℝ){t:ℝ→ℝ}(pos:∀ᶠ r in l,0<t r)(small:Tendsto t l (𝓝 0))

include H compact apart pos small in
theorem original {radius:ℝ}(cover:∀x∈K,‖x‖≤radius)(E p J:ℕ)(room:E+p≤J)(Q:ℕ)(order:J≤Q)
    (D:ℕ)(C:ℝ){δ:ℝ}(toll:0<δ):
    ∃j₀:ℕ,∀ᶠ r in l,∀j≥j₀,(j:ℝ)≤C*(-Real.log (t r))^D →
      ∃P:Handoff.Directory Z j (Handoff.Directory.budget G n d+Q),
      ∀(φ:Test n),tsupport φ⊆K → ∀(b:ℝ),0≤b → (∀x,‖φ x‖≤b) →
      ∀(w:Fin n→Γ→ℂ)(u:ℝ),|u|≤8*t r →
      (∀q≤Q,tested Z β (filed d β w) j q φ u=
        ∑k∈range (q+1),WilsonPositionRawEpoch.row Z P d φ (filed d β w) k*(u:ℂ)^k) ∧
      ∀L,(t r)^E*(∏i,∑a,‖w i a‖)≤L →
      ‖tested Z β (filed d β w) j Q φ u-tested Z β (filed d β w) j J φ u‖≤
        (L*(b*volume.real (closedBall (0:Points n) (radius+4*n))))*δ*(t r)^p:=by
  have program:=WilsonOriginalPublicPlantedTaylorFees.original Z H β compact apart l pos small
    (fun (a:Fin n→Γ) i=>axis (a i)) E p J room Q order D C toll
  obtain ⟨j₀,terms⟩:=program
  obtain ⟨j₁,opened⟩:=eventually_atTop.mp (H.onSchedule.eventually frontier.smaller)
  refine ⟨max j₀ j₁,?_⟩
  filter_upwards [terms,pos] with r testedRows positive
  intro j deep short
  obtain ⟨P,spent⟩:=testedRows j ((le_max_left ..).trans deep) short
  refine ⟨P,?_⟩
  intro φ housing b hb finite w u close
  obtain ⟨_,_,refund⟩:=spent (fun _=>φ) (fun _=>housing) (fun a=>∏i,w i (a i)) u close
  refine ⟨fun q hq=>WilsonOriginalPublicPlantedTaylorTest.printed Z β _ P q (by omega) φ u,?_⟩
  intro L debt
  have salary:=WilsonPositionProgramTrialCellVariation.original (Z.run.step j) φ
    (opened j ((le_max_right ..).trans deep)) hb (fun x hx=>cover _ (housing hx)) finite
  have money:0≤∏i,∑a,‖w i a‖:=prod_nonneg (fun _ _=>sum_nonneg fun _ _=>norm_nonneg _)
  have cost:0≤L:=(mul_nonneg (pow_nonneg positive.le _) money).trans debt
  have natural:0≤WilsonPositionProgramTrialCellVariation.mass (Z.run.step j) φ:=
    mul_nonneg (pow_nonneg (Z.run.step j).positive.le _) (sum_nonneg fun _ _=>norm_nonneg _)
  rw [printed Z β P Q le_rfl φ u w, printed Z β P J (by omega) φ u w]
  apply refund
  rw [doses,←mul_assoc]
  exact mul_le_mul debt salary natural cost

end YM.Integration.WilsonOriginalPublicPlantedTaylorPortfolio
