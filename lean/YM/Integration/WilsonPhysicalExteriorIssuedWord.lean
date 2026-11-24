import YM.Integration.WilsonPhysicalExteriorFiledWord
import YM.Integration.WilsonPhysicalExteriorCompensatedWindow

/-! On the preselected Wilson run, a quantitative comparison of the
complete independently inserted finite source and the honest contracted
continuum MS report, on the real and the prescribed auxiliary period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorIssuedWord
open Filter Real Finset PowerSeries Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet MS.Tone
open FVA2 Register FVAAlt2 Lobby RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorIndependentPrice WilsonPhysicalExteriorCompactWindow
open WilsonPhysicalExteriorChargedClocks WilsonPhysicalExteriorCompensatedWindow
open scoped Topology Classical
variable {G:Gauge}
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
variable {n:ℕ}

def difference (R:Run G) (M:M₀) (Q:Prescription B₀)
    (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B₀ (d i)) (c c':ℝ) (out:Fin n→Bool)
    (x:Fin n→QP) (μ:ℝ) (α eps:Fin n→ℝ) (u far:Fin n→Bool) (absolute side:Bool) (k j p:ℕ) : ℂ :=
  let W:=positions R c c' out x
  let T:=WilsonPhysicalExteriorFirstCut.scene R c W side 0
  let v:=fun i=>argument R c c' (α i) (u i) (far i) j
  let U:=nominal R μ absolute j
  coeff k (WilsonPhysicalExteriorFiledWord.finite R Q d b v eps U T (j,p)-
    WilsonPhysicalExteriorFiledWord.independent M Q d b v eps U T (j,p)
      (testP (WilsonPhysicalExteriorActualSides.field R c 0 W) (j,p)))

private theorem factored (R:Run G) (M:M₀) (Q:Prescription B₀) (hG:G.Simple)
    (taylor:TaylorOKPl M (Lobby.Table (basisR R) B₀) Q)
    (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B₀ (d i)) (c c':ℝ) (out:Fin n→Bool)
    (x:Fin n→QP) (μ:ℝ) (α eps:Fin n→ℝ) (u far:Fin n→Bool) (absolute side:Bool) (k j p:ℕ) :
    difference R M Q d b c c' out x μ α eps u far absolute side k j p =
      WilsonPhysicalExteriorSlotReference.ratio eps (exp (-WilsonPhysicalExteriorActualSides.time R c j)) (labels d b)*
        wordError R M Q d b c c' out x μ α u far absolute side k j p := by
  let W:=positions R c c' out x
  let T:=WilsonPhysicalExteriorFirstCut.scene R c W side 0
  let U:=nominal R μ absolute j
  let v:=fun i=>argument R c c' (α i) (u i) (far i) j
  let w:=((j,p):ℕ×ℕ)
  have ht:T.profile.θ w=WilsonPhysicalExteriorActualSides.time R c j:=by cases side <;> rfl
  have hy:U-T.profile.θ w=argument R c c' μ absolute false j:=by
    rw [ht];simp only [U,WilsonPhysicalExteriorCompensatedWindow.nominal,argument,Bool.false_eq_true,if_false,add_zero]
  obtain h:=WilsonPhysicalExteriorFiledWord.coefficient R M Q hG taylor d b v eps U T w
    (testP (WilsonPhysicalExteriorActualSides.field R c 0 W) w) k
  change coeff k (_-_) = _
  calc
    _ = WilsonPhysicalExteriorSlotReference.ratio eps (spacing T w) (labels d b) *
      WilsonPhysicalExteriorCompensatedQuote.total Q d b v (U-T.profile.θ w) (U-T.profile.θ w) k
        (fun a l=>WilsonPhysicalExteriorFirstCut.signed R M Q (fun i=>Lobby.owner (a i)) c W side l U w) := h
    _ = _ := by rw [hy,spacing,ht];rfl

/-- The price is on the entire signed word, not on separately selected
trials. All labels and admissible independent mark scales may be specified
after this same cutoff. -/
def Windows (R:Run G) (M:M₀) (Q:Prescription B₀) : Prop :=
  ∀ (n:ℕ) (I:Type) [Nonempty I] (d:Fin n→ℕ) (c c':ℝ) (out:Fin n→Bool) (x:I→Fin n→QP)
    (_:∀m,((R.family.S.block m).val:ℝ)≤log (RG16.Lambda R.family.path.levels m))
    (_:1<c') (_:c'<c) (_:c<2) (lo:ℕ→ℕ) (A δ:ℝ) (_:0<A) (_:0<δ)
    (_:∀z i,‖x z i‖≤A) (_:∀z i,out i=true → δ≤‖x z i‖)
    (_:∀z i l,i≠l → out i=out l → δ≤‖x z i-x z l‖)
    (μ:ℝ) (α:Fin n→ℝ) (q:ℝ) (k h:ℕ),
    ∀ᶠ j:ℕ in atTop,∀ b:(i:Fin n)→Plaid B₀ (d i),∀u far:Fin n→Bool,∀absolute:Bool,
    ∀z:I,∀side:Bool,∀p≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀eps:Fin n→ℝ,
    (∀i,exp (-WilsonPhysicalExteriorActualSides.time R c j)/WilsonPhysicalExteriorFirstCutScale.ratio R c' j≤eps i) →
    (WilsonPhysicalExteriorFirstCutScale.ratio R c' j)^h *
      ‖difference R M Q d b c c' out (x z) μ α eps u far absolute side k j p‖
      ≤exp (-q*RG16.Lambda R.family.path.levels j)

theorem billed (R:Run G) (M:M₀) (Q:Prescription B₀) (hG:G.Simple)
    (taylor:TaylorOKPl M (Lobby.Table (basisR R) B₀) Q)
    (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q) : Windows R M Q := by
  intro n I nonempty d c c' out x slow h₁ h₂ h₃ lo A δ ha hδ bound radial apart μ α q k h
  filter_upwards [WilsonPhysicalExteriorCompensatedWindow.measured (hG:=hG) R M Q rows d c c' out x slow h₁ h₂ h₃ lo A δ
    ha hδ bound radial apart μ α q k (h+∑i,d i)] with j hj b u far absolute z side p hp eps he
  let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c' j
  let e:=exp (-WilsonPhysicalExteriorActualSides.time R c j)
  have ht:0<T:=exp_pos _
  have hb:=WilsonPhysicalExteriorFiledWord.sharp d b e T eps (exp_pos _) ht he
  rw [factored R M Q hG taylor,norm_mul]
  let E:=wordError R M Q d b c c' out (x z) μ α u far absolute side k j p
  calc
    _≤ T^h*(T^(∑i,d i)*‖E‖):=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hb (norm_nonneg E)) (pow_nonneg ht.le h)
    _≤_:=by rw [←mul_assoc,←pow_add];exact hj b u far absolute z side p hp

/-- Buy the same full historical Match and the concrete rich prescription
on the original measured registry before any source menu or cutoff profile. -/
theorem funded (R:Run G) (hG:G.Simple) (N:WilsonPrescription G) (M:M₀) (dial:Bool)
    (hR:NativeFVAPlateau.Correlations R) :
    ∃ S:Prescription B₀,Main.Match N hG M S dial ∧
    ∃(Z:∀ b:Patch,b.Branches R.family.path.levels.clock.kernel G)
      (ledger:Lodge.Contract R (Oracle.books R.family.path.levels.clock.kernel) Z) (Q:Prescription B₀),
      Q.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR R) B₀) Q ∧
        WilsonPhysicalExteriorFundedPeriod.Periods R Z ledger Q ∧
        WilsonPhysicalExteriorFirstCutPrice.Rows R M Q ∧ Windows R M Q := by
  obtain ⟨S,hs,Z,L,Q,team,tp,periods,rows,_⟩:=WilsonPhysicalExteriorFundedRows.funded R hG N M dial hR
  exact ⟨S,hs,Z,L,Q,team,tp,periods,rows,billed R M Q hG tp rows⟩

end YM.Integration.WilsonPhysicalExteriorIssuedWord
end
