import YM.Integration.WilsonOriginalPublicRelativeGramAddresses
import YM.Integration.WilsonOriginalPublicRelativeGramFullBasis
import YM.Integration.WilsonViewerReportingGrid

/-! The actual physical reporting mesh produces the normalized finite
reflected Gram and its original uniform inverse price on all public fields
through the stated horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramReporting
open Filter Finset Function Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open Extraction Extraction.Banks RG17 Spec Table Table.Pairing Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonOriginalPublicRelativeGramPins (matrix)
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)

theorem original:
    ∃K:ℝ,0<K ∧ ∀(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(W:Finset E4){ℓ:Ultrafilter (ℕ×ℕ)}{g:ℝ→ℝ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g),
    G.Simple → Coupling G g → Leading F J →
    ∀ᶠ r in trail,let o:=ports R W (pointsAt a) (Γ.date r) r
      let M:=matrix R F a (fun _:Glyph B h=>h) J (fun i=>named R B h i) r r (Γ.date r)
        (fun _:Unit=>o) (fun _=>1) false
      Extraction.Order.grid R.family (Γ.date r) o∈generic 2 ∧
        IsUnit M.det ∧ ‖M⁻¹‖≤K:=by
  obtain ⟨K,kp,full⟩:=WilsonOriginalPublicRelativeGramFullBasis.original (L:=Unit) (Z:=ℝ) B h a
  refine ⟨K,kp,?_⟩
  intro R f S F J W ℓ g Γ simple temperature lead
  let δ:=fun r=>R.family.S.a (Γ.date r)/r
  let o:=fun r=>ports R W (pointsAt a) (Γ.date r) r
  have positive:∀ᶠ r in trail,0<r:=self_mem_nhdsWithin
  have dp:∀ᶠ r in trail,0<δ r:=positive.mono fun r rp=>div_pos (R.family.S.a_pos _) rp
  have upper:Tendsto (fun r=>g r^2) trail (𝓝 0):=by
    simpa only [zero_pow (by decide:2≠0)] using (Coupling.conforms simple temperature).pow 2
  have fine:Tendsto δ trail (𝓝 0):=squeeze_zero' (dp.mono fun _ hp=>hp.le) Γ.upper upper
  have sale:=full R F J trail id Γ.date (fun (r:ℝ) (_:Unit)=>o r) (fun _ _=>1) (fun _=>1)
    (fun r _=>shape W (pointsAt a) (δ r)) lead tendsto_id
    (positive.mono fun r rp _=>WilsonOriginalPublicRelativeGramAddresses.placed R W (pointsAt a) (Γ.date r) rp)
    (fun _=>WilsonOriginalPublicRelativeGramAddresses.limit W (pointsAt a) dp fine)
    (fun _=>tendsto_const_nhds) (by simp)
  filter_upwards [positive,sale] with r rp inv
  refine ⟨WilsonOriginalPublicRelativeGramAddresses.screened R W (pointsAt a) (Γ.date r) rp,?_⟩
  dsimp only at inv ⊢
  convert inv using 1 <;> congr! 4

end YM.Integration.WilsonOriginalPublicRelativeGramReporting
