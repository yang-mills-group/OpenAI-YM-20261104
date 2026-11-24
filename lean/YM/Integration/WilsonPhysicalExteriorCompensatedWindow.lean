import YM.Integration.WilsonPhysicalExteriorCompensatedQuote
import YM.Integration.WilsonPhysicalExteriorChargedClocks

/-! The signed MS finite-to-continuum error of a complete transported
Wilson source word on the original first mesh and an independent test
portfolio.  All field fees use the same filed prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorCompensatedWindow
open Filter Real Finset PowerSeries Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet MS.Tone
open FVA2 Register FVAAlt2 Lobby
open WilsonPhysicalExteriorRegisteredRows WilsonPhysicalExteriorIndependentPrice
open WilsonPhysicalExteriorChargedClocks WilsonPhysicalExteriorCompensatedQuote
open WilsonPhysicalExteriorCompactWindow
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "Λ₀" => RG16.Lambda R.family.path.levels
local notation "s₀" => R.family.S.scale
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
variable {n:ℕ}
def nominal (μ:ℝ) (absolute:Bool) (j:ℕ) := if absolute then μ+s₀ j else μ
def wordError (run:Run G) (sheet:M₀) (program:Prescription B₀)
    (d:Fin n→ℕ) (b:(i:Fin n)→Plaid B₀ (d i)) (c c':ℝ) (out:Fin n→Bool)
    (x:Fin n→QP) (μ:ℝ) (α:Fin n→ℝ) (u far:Fin n→Bool) (absolute side:Bool) (k j p:ℕ) : ℂ :=
  by
    let v:Fin n→ℝ:=fun i=>WilsonPhysicalExteriorChargedClocks.argument run c c' (α i) (u i) (far i) j
    let y:=WilsonPhysicalExteriorChargedClocks.argument run c c' μ absolute false j
    let W:=WilsonPhysicalExteriorCompactWindow.positions run c c' out x
    let old (a:WilsonPhysicalExteriorRegisteredRows.Array B₀ d) (l:ℕ):ℂ:=
      WilsonPhysicalExteriorFirstCut.signed run sheet program (fun i=>Lobby.owner (a i))
        c W side l (nominal run μ absolute j) (j,p)
    exact WilsonPhysicalExteriorCompensatedQuote.total program d b v y y k old

theorem measured {I:Type} [Nonempty I] {hG:G.Simple} (M:M₀) (Q:Prescription B₀)
    (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q) (d:Fin n→ℕ) (c c':ℝ)
    (out:Fin n→Bool) (x:I→Fin n→QP)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ) (A δ:ℝ) (ha:0<A) (hδ:0<δ)
    (bound:∀z i,‖x z i‖≤A) (radial:∀z i,out i=true→δ≤‖x z i‖)
    (apart:∀z i l,i≠l → out i=out l → δ≤‖x z i-x z l‖)
    (μ:ℝ) (α:Fin n→ℝ) (q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀ b:(i:Fin n)→Plaid B₀ (d i),∀u far:Fin n→Bool,∀absolute:Bool,
      ∀ z:I,∀side:Bool,∀ p≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      (WilsonPhysicalExteriorFirstCutScale.ratio R c' j)^h*
        ‖wordError R M Q d b c c' out (x z) μ α u far absolute side k j p‖≤exp (-q*Λ₀ j) := by
  obtain ⟨C,hC,m,quote⟩:=WilsonPhysicalExteriorCompensatedQuote.paid Q d k
  let big:=q+3*(m:ℝ)+1
  let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c'
  have profiles : ∀ᶠ j:ℕ in atTop,∀a:Array B₀ d,∀l:Fin (k+1),
      ∀z:I,∀side:Bool,∀p≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀abs:Bool,
      (T j)^h*‖WilsonPhysicalExteriorFirstCut.signed R M Q (fun i=>Lobby.owner (a i)) c
        (positions R c c' out (x z)) side l.val (nominal R μ abs j) (j,p)‖≤exp (-big*Λ₀ j) := by
    apply Filter.eventually_all.mpr;intro a
    apply Filter.eventually_all.mpr;intro l
    filter_upwards [WilsonPhysicalExteriorCompactWindow.measured (hG:=hG) R M Q rows (fun i=>Lobby.owner (a i)) c c' out x
      slow h₁ h₂ h₃ lo A δ ha hδ bound radial apart μ big l.val h] with j hj z side p hp abs
    cases abs
    · exact (hj z side p hp).1
    · exact (hj z side p hp).2
  let fees:=WilsonPhysicalExteriorIndependentPrice.clock α μ μ
  have entrance:=WilsonPhysicalExteriorChargedClocks.all R hG slow (h₁.trans h₂).le h₂.le h₃.le fees
  have growth:=tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)
  filter_upwards [profiles,entrance,growth.eventually_ge_atTop C] with j hprof hclock hconstant b u far abs z side p hp
  let v:=fun i=>argument R c c' (α i) (u i) (far i) j
  let y:=argument R c c' μ abs false j
  let X:=WilsonPhysicalExteriorIndependentPrice.clock v y y
  let bit (u:Fin n→Bool) (abs:Bool) (a:Fin n×Fin 3):Bool:=(![u a.1,abs,abs]:Fin 3→Bool) a.2
  have eco:length X≤exp (3*Λ₀ j) := by
    have eq:X=(fun i=>argument R c c' (fees i) (bit u abs i) (bit far false i) j):=by
      funext i;obtain ⟨a,l⟩:=i;fin_cases l <;> rfl
    rw [eq];exact hclock (bit u abs) (bit far false)
  let E:=fun (a:Array B₀ d) l=>WilsonPhysicalExteriorFirstCut.signed R M Q (fun i=>Lobby.owner (a i)) c
    (positions R c c' out (x z)) side l (nominal R μ abs j) (j,p)
  have tnon:0≤T j:= (exp_pos _).le
  have bare:=quote b v y y ((T j)^h) (exp (-big*Λ₀ j)) (pow_nonneg tnon h) (exp_pos _).le E
    (fun a l hl=>hprof a ⟨l,by omega⟩ z side p hp abs)
  have len:0≤length X:=by unfold length;positivity
  have fee:=mul_le_mul (show C≤exp (Λ₀ j) from hconstant) (pow_le_pow_left₀ len eco m)
    (pow_nonneg len m) (exp_pos _).le
  calc
    _ ≤ C*(length X)^m*exp (-big*Λ₀ j) := bare
    _ ≤ exp (Λ₀ j)*(exp (3*Λ₀ j))^m*exp (-big*Λ₀ j) :=
      mul_le_mul_of_nonneg_right fee (exp_pos _).le
    _ = _:=by rw [←exp_nat_mul,←exp_add,←exp_add];congr 1;dsimp [big];ring

end YM.Integration.WilsonPhysicalExteriorCompensatedWindow
end
