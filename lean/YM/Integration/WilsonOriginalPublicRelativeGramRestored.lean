import YM.Integration.WilsonOriginalPublicRelativeGramWideStation
import YM.Integration.WilsonOriginalPublicRelativeGramBranch

/-! Restoring the smaller-date frame to the common signed public axes costs
the true opposite transport only after the signed two-date comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramRestored
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramTransport (transition)
open WilsonOriginalPublicRelativeGramPosted (Dated)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {I:Type}[Fintype I][DecidableEq I]
local notation "Mat" => Matrix I I ℂ

theorem estimate (A B T U:Mat)(p c:ℝ)(rank:IsUnit A.det)(undo:T*U=1)
    (tested:‖T-A⁻¹*B‖≤p)(fee:‖U‖≤c):‖B*U-A‖≤‖A‖*p*c:=by
  have identity:A*(A⁻¹*B-T)*U=B*U-A:=by
    rw [Matrix.mul_sub,Matrix.mul_nonsing_inv_cancel_left _ _ rank,Matrix.sub_mul,
      Matrix.mul_assoc,undo,Matrix.mul_one]
  rw [←identity]
  have first:‖A*(A⁻¹*B-T)‖≤‖A‖*p:=(norm_mul_le ..).trans (mul_le_mul_of_nonneg_left
    (by rwa [norm_sub_rev]) (norm_nonneg _))
  exact (norm_mul_le ..).trans (mul_le_mul first fee (norm_nonneg _) ((norm_nonneg _).trans first))

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (h:ℕ)(J:ℝ→tower S)(basis:Module.Basis I ℂ ((Spin.comparator R.family.book).Field h))
    {L:Type}[Fintype L](W:Initialize G)(sale:Dated (L:=L) R W (fun _:I=>h))

omit [Fintype L] in
theorem original (lead:Leading F J):
    ∃(C:ℝ)(k:ℕ),0<C ∧ ∀ᶠr in trail,∀E:ℝ,1≤E → ∀p:ℝ,∀z:ℕ×ℕ,
      IsUnit (sale.frame false z).det →
      ‖transition R h J basis r (r/E)-(sale.frame false z)⁻¹*sale.frame true z‖≤p →
      ‖sale.frame true z*transition R h J basis (r/E) r-sale.frame false z‖≤
        ‖sale.frame false z‖*p*(C*E^k):=by
  obtain ⟨C,k,cp,paid⟩:=WilsonOriginalPublicRelativeGramOptical.original R F h J basis lead
  refine ⟨C,k,cp,?_⟩
  filter_upwards [paid] with r money
  intro E ep p z rank gap
  apply estimate _ _ (transition R h J basis r (r/E)) _ _ _ rank _ gap (money E ep).1
  rw [WilsonOriginalPublicRelativeGramOptical.compose,WilsonOriginalPublicRelativeGramOptical.same]

variable {Z:Type}{l:Filter Z}

theorem align (A B U:Z→Mat){D:Mat}(cash:Z→ℝ)
    (reference:Tendsto A l (𝓝 D))(small:Tendsto cash l (𝓝 0))
    (twoDates:∀ᶠz in l,‖B z*U z-A z‖≤‖A z‖*cash z):
    Tendsto (fun z=>B z*U z) l (𝓝 D):=by
  have fee:Tendsto (fun z=>‖A z‖*cash z) l (𝓝 0):=by simpa only [mul_zero] using reference.norm.mul small
  apply Metric.tendsto_nhds.mpr
  intro e ep
  have ep2:0<e/2:=half_pos ep
  filter_upwards [twoDates,fee.eventually (gt_mem_nhds ep2),
    Metric.tendsto_nhds.mp reference (e/2) ep2] with z joint cheap close
  calc
    dist (B z*U z) D ≤ dist (B z*U z) (A z)+dist (A z) D:=dist_triangle ..
    _ ≤ ‖A z‖*cash z+dist (A z) D:=add_le_add (by rw [dist_eq_norm]; exact joint) le_rfl
    _ < e/2+e/2:=add_lt_add cheap close
    _ = e:=by ring

end YM.Integration.WilsonOriginalPublicRelativeGramRestored
