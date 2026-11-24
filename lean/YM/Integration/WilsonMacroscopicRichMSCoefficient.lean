import YM.FVA2.O.Canon.Docket
import YM.Integration.WilsonMatrixTicketLanesReportedRunMS
import YM.Integration.WilsonMacroscopicRichIndependentHearing

/-! Assemble the independently specified unit-shape MS OPE coefficients in the original
Maxwell field basis. All incoming and outgoing filtration components are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMSCoefficient
open Function Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.O FVA2.ColorCode RegulatorIR.FVAAlt2.Lodge Extra.FD OPE.Levy
open FVA2.Scale Extraction Table Spec Climb PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "B₀" => Press.portDeck G

def coordinate (h:ℕ)(v:(Bel R.family.book).Field h)(b:Glyph B₀ h):ℂ:=
  (Daylight B₀ h).repr (exactField R.family.labels h v) b

def coefficient (M:MS_Data G (Position.OpenAxis.Plot B₀)) {n h:ℕ}(d:Fin n→ℕ)
    (v:(i:Fin n)→(Bel R.family.book).Field (d i))(μ:ℝ)(x:Points n)(t:ℝ)(q:ℕ)(b:Glyph B₀ h):ℂ:=
  ∑a:(i:Fin n)→Glyph B₀ (d i), (∏i,coordinate R (d i) (v i) (a i))*
    ∑k∈Finset.range (q+1), (t:ℂ)^k*
      PowerSeries.coeff k (Canon.FarCoefficients (Equator.wave μ M) (fun i=>Dframe.flash (a i)) x (Dframe.flash b))

def field (M:MS_Data G (Position.OpenAxis.Plot B₀)) {n:ℕ}(h:ℕ)(d:Fin n→ℕ)
    (v:(i:Fin n)→(Bel R.family.book).Field (d i))(μ:ℝ)(x:Points n)(t:ℝ)(q:ℕ):(Bel R.family.book).Field h:=
  (exactField R.family.labels h).symm (∑b:Glyph B₀ h,coefficient R M d v μ x t q b • (Daylight B₀ h) b)

theorem filed (M:MS_Data G (Position.OpenAxis.Plot B₀)) {n:ℕ}(h:ℕ)(d:Fin n→ℕ)
    (v:(i:Fin n)→(Bel R.family.book).Field (d i))(μ:ℝ)(x:Points n)(t:ℝ)(q:ℕ)(b:Glyph B₀ h):
    coordinate R h (field R M h d v μ x t q) b=coefficient R M d v μ x t q b:=by
  unfold field coordinate
  simp [Finsupp.single_apply]

def shape {n:ℕ}(m:ℕ)(ρ:ℝ)(x:Fin n→Lattice.Cover):Points n:=
  WithLp.toLp 2 (fun i=>(R.family.S.a m*ρ)⁻¹ • R.family.S.gridPoint m (x i))

theorem position {n:ℕ}(m:ℕ)(ρ:ℝ)(_hr:0<ρ)(x:Fin n→Lattice.Cover)(i:Fin n):
    (R.family.S.a m*ρ) • shape R m ρ x i=R.family.S.gridPoint m (x i):=by
  change (R.family.S.a m*ρ) • ((R.family.S.a m*ρ)⁻¹ • _) = _
  rw [smul_smul,mul_inv_cancel₀ (mul_pos (R.family.S.a_pos m) _hr).ne',one_smul]

end YM.Integration.WilsonMacroscopicRichMSCoefficient
