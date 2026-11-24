import YM.Integration.WilsonLocalConditionalResidue

/-! A multiplicative positive-coupling comparison of conditional densities
on the actual reporting forest, with unchanged exterior and held coarse input. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalTerminalWeights
open Function Finset Set Lattice RG Tree Wilson RG16 Precision PertExtension PertExtension.Series Push.BetaTransport
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalPlaquetteForest WilsonLocalPlaquetteField WilsonLocalPlaquetteAction WilsonLocalConditionalResidue
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f}

def close (x y D:ℝ) : Prop := 0<x ∧ 0<y ∧ |Real.log x-Real.log y|≤D ∧ Real.exp (-D)*y≤x ∧ x≤Real.exp D*y

def quoted (P:ChartRatio G) (p:ℕ) (δ H W β:ℝ) (ρ K:Config G f→ℝ) (T:Forest S.ratio)
    (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color) :=
  let g:=(Real.sqrt β)⁻¹
  (∀i,g*‖X i‖≤δ ∧ g*‖Y i‖≤δ)→
  close (weight P ρ T B v g X/weight P ρ T B v g Y) (fitted P p β g K T B v X Y) (expense p H W g X Y)

theorem ledger {a k h w z:ℝ} (hk:0<k) (given:|Real.log a-Real.log k-h+w|≤z) :
    |Real.log a-Real.log (k*Real.exp (h-w))|≤z := by
  rw [Real.log_mul hk.ne' (Real.exp_pos _).ne',Real.log_exp]
  convert given using 2;ring

theorem submit (P:ChartRatio G) (p:ℕ) {δ H W β:ℝ} (hW:0≤W) (hβ:0<β) (ρ K:Config G f→ℝ)
    (inputs:∀U,0<K U ∧ 0<ρ U) (T:Forest S.ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color)
    (budget:WilsonLocalTerminalConditional.estimate P p δ H W β ρ K T B v X Y)
    (jacobian:let g:=(Real.sqrt β)⁻¹;(∀i,g*‖X i‖≤δ ∧ g*‖Y i‖≤δ)→
      0<Chart.jacobian P (g•X) ∧ 0<Chart.jacobian P (g•Y)) :
    quoted P p δ H W β ρ K T B v X Y := by
  let E:=moving T B
  let g:=(Real.sqrt β)⁻¹
  let U:=WilsonLocalConditionalResidue.position T B v g
  let source:=weight P ρ T B v g X/weight P ρ T B v g Y
  let model:=fitted P p β g K T B v X Y
  let D:=expense p H W g X Y
  have hg:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  dsimp only [quoted];intro room
  have J:=jacobian room
  have truePos:0<source:=div_pos (mul_pos J.1 (inputs (U X)).2) (mul_pos J.2 (inputs (U Y)).2)
  have kernel:0<K (U X)/K (U Y):=div_pos (inputs _).1 (inputs _).1
  have modelPos : 0 < model:=mul_pos kernel (Real.exp_pos _)
  have priced:=ledger kernel (budget room)
  have tight:=WilsonLocalPlaquetteForestBilling.amount T E (p+2) X Y
  have signed:|Real.log source-Real.log model|≤D := priced.trans (by
    refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left tight (mul_nonneg hW (pow_nonneg hg.le (p+1))))).trans_eq ?_
    change _=expense p H W g X Y
    unfold expense;ring)
  exact ⟨truePos,modelPos,signed,relative truePos modelPos signed⟩

theorem original (P:ChartRatio G) (hp:LocalRatio P) (p:ℕ) :
    ∃δ H W:ℝ,0<δ ∧ δ≤1/2 ∧ 0≤H ∧ 0≤W ∧ ∀(R:Run G) (m per:ℕ) (V:Config G (R.family.side m per))
    (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color),
    let n:=m+1
    let β:=(R.family.path.rep n per n).beta
    quoted P p δ H W β (actualConditionalDensity R.family n per m V)
      (fun U=>(R.family.path.levels.clock.op m per).density β U V) T B v X Y := by
  obtain ⟨δ,H,W,hδ,half,hH,hW,buy⟩:=WilsonLocalTerminalConditional.original P hp p
  obtain ⟨r,C,hr,_,haar⟩:=WilsonLocalHaarOrder.original P hp p
  refine ⟨min δ r,H,W,lt_min hδ hr,(min_le_left ..).trans half,hH,hW,?_⟩
  intro R m per V T B v X Y
  let n:=m+1
  have hβ : 0<(R.family.path.rep n per n).beta := Overlay.beta_positive R.makes.wilson (show n≤n from le_rfl)
  refine submit P p hW hβ _ _
    (positive R.family R.makes (m+1) per m (Nat.lt_succ_self m) V) T B v X Y ?_ ?_
  · dsimp only [WilsonLocalTerminalConditional.estimate];intro room
    exact buy R m per V T B v X Y (fun i=>⟨(room i).1.trans (min_le_left ..),(room i).2.trans (min_le_left ..)⟩)
  · dsimp only;intro room
    have sold:=haar (↥(moving T B)) X Y _ (inv_pos.mpr (Real.sqrt_pos.mpr hβ))
      (fun i=>⟨(room i).1.trans (min_le_right ..),(room i).2.trans (min_le_right ..)⟩)
    exact ⟨sold.1,sold.2.1⟩

end YM.Integration.WilsonLocalTerminalWeights
