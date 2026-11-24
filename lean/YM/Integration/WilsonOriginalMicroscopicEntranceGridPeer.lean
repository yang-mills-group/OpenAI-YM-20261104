import YM.Integration.WilsonOriginalMicroscopicEntranceGridRow
import YM.Integration.WilsonAddressedRestartedPeerRead

/-! A signed source on the enrolled earlier grid, heard against a specified
ordinary cofactor on the original positive Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceGridPeer
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent Marker
open WilsonOriginalMicroscopicEntranceGridRow (factor signed)
open WilsonThermometerUnitFilingCoarse (reading)
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f u:ℕ}
local notation "C₀" => R.family
local notation "P" => R.family.path.rep N p f
local notation "X" i:max => Config G (R.family.side i p)

def held (Z:X f→ℂ)(uf:u≤f)(W:X u):ℂ:=
    (((C₀).path.rep N p u).eval W:ℂ)⁻¹*gust (C₀).path N p f Z u uf W

theorem original (live:f≤N)(a:Fin 3)(o:Site ((C₀).side f p))(z:store C₀ (d a) p f)
    (H:X f→ℂ)(B:ℝ)(registered:X f→ℂ)(filed:WilsonAddressedRestartedFiled.Filed R (d a) N p f o registered B z)
    (bill:Integrable (fun U=>registered (Lattice.translate o U)*H U) (prior G _))
    (uf:u≤f)(W:X u):
    actualTransport C₀ (N:=N) (fun U=>signed R d (N:=N) a o z U*H U) uf W=
      -(factor R d f a)*held R (N:=N) (fun U=>registered (Lattice.translate o U)*H U) uf W:=by
  let Z:=fun U:X f=>registered (Lattice.translate o U)*H U
  let c:=-(factor R d f a)
  have same:(fun U=>(P).eval U • (signed R d (N:=N) a o z U*H U))=c • Z:=by
    funext U
    have ne:((P).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    have af:(R.family.S.a f:ℂ)≠0:=by exact_mod_cast (R.family.S.a_pos f).ne'
    simp only [signed,Complex.real_smul,Pi.smul_apply,smul_eq_mul,c,WilsonOriginalMicroscopicEntranceGridRow.factor,Z,filed.field,Function.comp_apply]
    field_simp [ne,af]
  unfold actualTransport held
  rw [same,scale R c Z bill uf,Complex.real_smul,Complex.ofReal_inv]
  change _*(c*_)=c*(_*_)
  ring

theorem flat (live:f≤N)(a:Fin 3)(o:Site ((C₀).side f p))(z:store C₀ (d a) p f)
    (H:X f→ℂ)(B:ℝ)(registered:X f→ℂ)(filed:WilsonAddressedRestartedFiled.Filed R (d a) N p f o registered B z)
    (bill:Integrable (fun U=>registered (Lattice.translate o U)*H U) (prior G _))(uf:u≤f):
    actualTransport C₀ (N:=N) (fun U=>signed R d (N:=N) a o z U*H U) uf 1=
      -(factor R d f a)*reading R (N:=N) (fun U=>registered (Lattice.translate o U)*H U) u uf:=
  original R d live a o z H B registered filed bill uf 1

end YM.Integration.WilsonOriginalMicroscopicEntranceGridPeer
end
