import YM.Integration.WilsonMeasuredPublicEntranceWeakRaw
import YM.Integration.WilsonMeasuredPublicEntranceDatedGauge

/-! The original ultrafilter fixes the complete physical linear frame of a presold
raw chart. A later weak extraction on those same cutoffs uses this exact frame. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeFrame
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE Spin
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS
open Trace.Terrace Trace.Over FVA2 FVA2.Register
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Further.CorrectedLift
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {d:ℕ}(ℓ:Ultrafilter (ℕ×ℕ))
set_option quotPrecheck false
local notation "D" => (Cells.standard C).Field
local notation "Sheet"=> ((ℕ×ℕ)→D d→L[ℂ] C.label d)

def Priced (raw:Sheet)(frame:change S d):Prop:=
  ∃Y:D d→L[ℂ] C.label d,Tendsto raw (ℓ:Filter _) (𝓝 Y) ∧ ∀z,frame z=S.project d (Y z)

def selected (raw:Sheet)(fallback:change S d):change S d:=
  if h:∃U:change S d,Priced ℓ raw U then h.choose else fallback

theorem unique {raw:Sheet}{U W:change S d}(p:Priced ℓ raw U)(q:Priced ℓ raw W):U=W:=by
  obtain ⟨X,hx,ux⟩:=p
  obtain ⟨Y,hy,wy⟩:=q
  have same:X=Y:=tendsto_nhds_unique hx hy
  ext v
  rw [ux,wy,same]

theorem filed {raw:Sheet}(fallback:change S d){U:change S d}(p:Priced ℓ raw U):
    selected ℓ raw fallback=U:=by
  have yes:∃W:change S d,Priced ℓ raw W:=⟨U,p⟩
  exact (dif_pos yes).trans (unique ℓ yes.choose_spec p)

theorem meters {J:Scaling S}{V:∀i,Vane C i}{Y:∀d:ℕ,ℕ→D d→L[ℂ] C.label d}
    {H:(Cells.standard C).Hierarchy}(paid:Gondola f H J ℓ V Y)(d:ℕ):
    ∀ᶠ i:ℕ in atTop,∀fallback:change S d,selected ℓ (heightV V i d) fallback=J.U i d:=by
  filter_upwards [paid.terminal d] with i native fallback
  exact filed ℓ fallback ⟨Y d i,native⟩

def atRadius {radius:ℝ}(horizon:Set.Ioc (0:ℝ) radius→ℕ)
    (survey:∀s,Vane C (horizon s))(fallback:ℝ→tower S)(r:ℝ):tower S:=fun d=>
  if hs:r∈Set.Ioc (0:ℝ) radius then
    let s:Set.Ioc (0:ℝ) radius:=⟨r,hs⟩
    if top:d≤horizon s then
      selected ℓ (fun p=>(survey s).wheel.atCut p ⟨d,Nat.lt_succ_of_le top⟩) (fallback r d)
    else fallback r d
  else fallback r d

theorem at_site {radius:ℝ}(horizon:Set.Ioc (0:ℝ) radius→ℕ)
    (survey:∀s,Vane C (horizon s))(fallback:ℝ→tower S)(s:Set.Ioc (0:ℝ) radius)(top:d≤horizon s)
    {U:change S d}(sold:Priced ℓ (fun p=>(survey s).wheel.atCut p ⟨d,Nat.lt_succ_of_le top⟩) U):
    atRadius ℓ horizon survey fallback s.val d=U:=by
  simpa only [atRadius,dif_pos s.property,dif_pos top] using filed ℓ (fallback s.val d) sold

end YM.Integration.WilsonMeasuredPublicEntranceNativeFrame
end
