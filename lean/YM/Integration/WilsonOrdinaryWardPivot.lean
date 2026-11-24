import YM.Integration.WilsonOrdinaryAdmissibleEquation

/-! The true, independently prescribed, symmetry-admissible normalized
two-field equation on the same original Yang--Mills continuum. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryWardPivot
open Function Filter Matrix Pert Pert.Position MS MS.Theater MS.Menus MS.Land MS.Local.Physical
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Table Spec Climb PhysMS Maxwell Trace.Pilot
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
open WilsonMacroscopicRichMeasuredGram WilsonMacroscopicRichRegister
open WilsonOrdinaryAdmissibleEquation WilsonOrdinaryWardSpace
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (B : Deck G) {O : Booked B} (M : MS_Data G O) (F : Final C f S)
  (J : ℝ→PhysMS.tower S) (d : ℕ) (g : Test 2) (μ : ℝ)
  (H : (Bel C.book).Hierarchy) (γ : ℝ→ℝ)
local notation "Iₕ" => Glyph B d
local notation "K₀" => MSSeparatedTestGram.matrix M d μ 0 g
local notation "E₀" => WilsonOrdinaryWardSpace.mask B d
local notation "D₀" => WilsonOrdinaryWardSpace.directions C B d H
local notation "W₀" => WilsonMacroscopicRichMeasuredGram.bank B F J d g
local notation "P₀" => WilsonOrdinaryAllOrderPivot.curve B M d g μ

def request (r : ℝ) : Matrix Iₕ Iₕ ℂ := W₀ r+E₀*(P₀ (γ r) - W₀ r)
def change (r : ℝ) : D₀ := correction D₀ (W₀ r) (request B M F J d g μ γ r) K₀⁻¹
def committed (r : ℝ) : Matrix Iₕ Iₕ ℂ := (1+(change B M F J d g μ H γ r).val)*W₀ r
def field (r : ℝ) : (Bel C.book).Field d ≃ₗ[ℂ] S.Field d :=
  WilsonOrdinaryPivotFrame.frame B F J d g (committed B M F J d g μ H γ) r

theorem buys (leading : PhysMS.Leading F J) (hG : G.Simple) (live : IsUnit K₀) (hγ : Coupling G γ) :
    Tendsto (change B M F J d g μ H γ) trail (𝓝 0) ∧ ∀ᶠ r in trail,
    select D₀ ((committed B M F J d g μ H γ r-request B M F J d g μ γ r)*K₀⁻¹)=0 := by
  have obs := WilsonMacroscopicRichMeasuredGram.original B F J leading M d g μ
  have target := WilsonOrdinaryAllOrderPivot.lands B M d g μ hγ hG
  have req : Tendsto (request B M F J d g μ γ) trail (𝓝 K₀) := by
    change Tendsto (fun r=>W₀ r+E₀*(P₀ (γ r)-W₀ r)) trail (𝓝 K₀)
    simpa only [sub_self,mul_zero,add_zero] using obs.add ((tendsto_const_nhds (x:=E₀)).mul (target.sub obs))
  have paid := WilsonOrdinaryAdmissibleEquation.solved D₀ live W₀ (request B M F J d g μ γ) obs req
  exact ⟨paid.1,paid.2.mono (fun _ h=>h.2)⟩

theorem arrives (leading : PhysMS.Leading F J) (hG : G.Simple) (live : IsUnit K₀) (hγ : Coupling G γ) :
    Tendsto (committed B M F J d g μ H γ) trail (𝓝 K₀) := by
  have small := (buys B M F J d g μ H γ leading hG live hγ).1
  have valued : Tendsto (fun r=>(change B M F J d g μ H γ r).val) trail (𝓝 0) :=
    continuous_subtype_val.continuousAt.tendsto.comp small
  have obs := WilsonMacroscopicRichMeasuredGram.original B F J leading M d g μ
  change Tendsto (fun r=>(1+(change B M F J d g μ H γ r).val)*W₀ r) trail (𝓝 K₀)
  simpa only [add_zero,one_mul] using ((tendsto_const_nhds (x:=(1 : Matrix Iₕ Iₕ ℂ))).add valued).mul obs

theorem relative (leading : PhysMS.Leading F J) (hG : G.Simple) (live : IsUnit K₀) (hγ : Coupling G γ)
    (v : (Bel C.book).Field d) : Tendsto (fun r=>(J r d).symm (field B M F J d g μ H γ r v)) trail (𝓝 v) :=
  (WilsonOrdinaryPivotFrame.calibrated B M F J d g leading μ live _ (arrives B M F J d g μ H γ leading hG live hγ)).2 v

theorem paid (leading : PhysMS.Leading F J) (hG : G.Simple) (live : IsUnit K₀) (hγ : Coupling G γ) :
    ∀ᶠ r in trail,∀ v,field B M F J d g μ H γ r v=J r d (act C B d (1+(change B M F J d g μ H γ r).val) v) := by
  let A := committed B M F J d g μ H γ
  let T := WilsonMacroscopicRichFree.basis C B d
  have yes : (K₀).det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp live)
  have dp := (continuous_id.matrix_det.continuousAt (x:=K₀)).tendsto.comp (arrives B M F J d g μ H γ leading hG live hγ)
  have dw := (WilsonMacroscopicRichMeasuredGram.invertible B F J leading M d g μ live).1
  filter_upwards [dp.eventually_ne yes,dw] with r good invertible
  intro v
  have right := Matrix.mul_nonsing_inv (W₀ r) ((Matrix.isUnit_iff_isUnit_det _).mp invertible)
  have source := WilsonOrdinaryPivotFrame.coordinates B F J d g A r
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr good)) invertible v
  change T.equivFun ((J r d).symm (field B M F J d g μ H γ r v))=
    (((1+(change B M F J d g μ H γ r).val)*W₀ r)*(W₀ r)⁻¹).vecMul (T.equivFun v) at source
  rw [Matrix.mul_assoc,right,mul_one] at source
  apply (J r d).symm.injective;rw [LinearEquiv.symm_apply_apply];apply T.equivFun.injective
  change _=T.equivFun (T.equivFun.symm _);rw [LinearEquiv.apply_symm_apply];exact source

def reading (U : (Bel C.book).Field d ≃ₗ[ℂ] S.Field d) {r : ℝ} (hr : 0<r) : Matrix Iₕ Iₕ ℂ :=
  fun a b=>(exterior B J g hr b).charge F d (U (WilsonMacroscopicRichFree.basis C B d a))

theorem actual (leading : PhysMS.Leading F J) (hG : G.Simple) (live : IsUnit K₀) (hγ : Coupling G γ) :
    ∀ᶠ r in trail,∀ hr:0<r,reading B F J d g (field B M F J d g μ H γ r) hr=committed B M F J d g μ H γ r := by
  have reads := (WilsonOrdinaryPivotFrame.calibrated B M F J d g leading μ live _ (arrives B M F J d g μ H γ leading hG live hγ)).1
  filter_upwards [reads] with r all
  intro hr;ext a b
  rw [reading,field,all hr]
  simp [Matrix.vecMul,dotProduct]

end YM.Integration.WilsonOrdinaryWardPivot
end

