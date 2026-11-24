import YM.Integration.WilsonLocalInheritedRatio

/-! An interior step retains its full incoming normalized effective weight
relative to the original Wilson action. The local Taylor comparison only
changes the Haar and Wilson terms, on the same true measured conditional. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalInheritedWeights
open Finset Set Lattice RG Tree Wilson RG16 Precision PertExtension PertExtension.Series
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonLocalPlaquetteForest WilsonLocalPlaquetteField WilsonLocalPlaquetteAction WilsonLocalConditionalResidue
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}

theorem original (P:ChartRatio G) (hp:LocalRatio P) (p:ℕ) :
    ∃δ H W:ℝ,0 < δ ∧ δ ≤ 1/2 ∧ 0 ≤ H ∧ 0 ≤ W ∧ ∀(R:Run G) (m N per:ℕ),m < N→
    ∀(V:Config G (R.family.side m per)) (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color),
    let β:=R.family.path.β N per (m+1)
    WilsonLocalTerminalWeights.quoted P p δ H W β (actualConditionalDensity R.family N per m V)
      (WilsonLocalInheritedRatio.rest R.family N per m V) T B v X Y := by
  obtain ⟨r,H,hr,hH,haar⟩:=WilsonLocalHaarOrder.original P hp p
  obtain ⟨W,hW,wilson⟩:=WilsonLocalPlaquetteReporting.received G p
  let δ:=min r (1/2)
  have half:δ ≤ 1/2:=min_le_right .. 
  refine ⟨δ,H,W,lt_min hr (by norm_num),half,hH,hW,?_⟩
  intro R m N per hm V T B v X Y
  let E:=moving T B
  let β:=R.family.path.β N per (m+1)
  let g:=(Real.sqrt β)⁻¹
  let U:=WilsonLocalConditionalResidue.position T B v g
  have hβ:0 < β:=Overlay.beta_positive R.makes.wilson hm
  have receipt (room:∀i,g*‖X i‖ ≤ δ ∧ g*‖Y i‖ ≤ δ) :=
    haar (↥E) X Y g (inv_pos.mpr (Real.sqrt_pos.mpr hβ))
      (fun i=>⟨(room i).1.trans (min_le_left ..),(room i).2.trans (min_le_left ..)⟩)
  refine WilsonLocalTerminalWeights.submit P p hW hβ _ _
    (WilsonLocalInheritedRatio.positive R N per m hm V) T B v X Y ?_ ?_
  · dsimp only [WilsonLocalTerminalConditional.estimate];intro room
    have solvent:=receipt room
    have small:δ < 1:=half.trans_lt (by norm_num)
    have action:=wilson _ _ _ T B v X Y β hβ (fun i=>⟨(room i).1.trans_lt small,(room i).2.trans_lt small⟩)
    have law:=WilsonLocalInheritedRatio.logarithm R N per m hm V (U X) (U Y) _ _ solvent.1 solvent.2.1
    dsimp only at law
    change |Real.log ((Chart.jacobian P (g•X)*actualConditionalDensity R.family N per m V (U X))/
      (Chart.jacobian P (g•Y)*actualConditionalDensity R.family N per m V (U Y)))-_-_+_| ≤ _
    rw [law];exact WilsonLocalTerminalConditional.price solvent.2.2 action
  · dsimp only;intro room
    exact ⟨(receipt room).1,(receipt room).2.1⟩

end YM.Integration.WilsonLocalInheritedWeights
