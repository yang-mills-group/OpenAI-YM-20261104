import YM.Integration.WilsonOriginalPublicRelativeGramWide
import YM.Integration.WilsonOriginalPublicRelativeGramRough

/-! Wider physical reflector at t and elected thermal reference at t/E.

 Original two-site BEFORE-K payments price the later compensated inverse
on the genuine reporting grid. The unit and every lower coordinate are read
together with the chosen nonconstant fields. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramWideStation
open Filter Finset Lattice Wilson RG Source Labels Cells OPE
open PhysicalNext.Repeat.Legato Extraction Extraction.Banks RG17 Spec Table Table.Pairing
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical Trace.Pilot PhysMS
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonOriginalPublicRelativeGramPins (matrix cutoff)
open WilsonOriginalPublicRelativeGramPosted (Dated submitted deposits)
open WilsonOriginalPublicRelativeGramTransport (transition)
open WilsonOriginalPublicRelativeGramJoined (fee)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(site:ℕ)(t r K:ℝ)(avoid:Finset E4)
local notation "I" => Glyph B h
local notation "ω" => (fun _:Unit=>ports R avoid (pointsAt a) site t)
local notation "one" => (fun _:Unit=>(1:ℂ))
local notation "P" => named R B h

def Receives:Prop:=
  ∀(W:Initialize G)(s:ℝ)(Y:Bool→(ℕ×ℕ)→I→R.family.label h)(b:Bool→I→R.family.label h)
    (sale:Dated (L:=Unit) R W (fun _:I=>h))(cash:I→I→ℝ)(σ old:Bool→I→I→ℝ)(η price:ℝ),
  (∀t i,Tendsto (fun z=>Y t z i) (ℓ:Filter (ℕ×ℕ)) (𝓝 (b t i))) →
  (∀t i,S.project h (b t i)=J (cond t s r) h (P i)) →
  (∀ᶠ z:ℕ×ℕ in f.fuse,∀i j,‖cutoff R a (fun _:I=>h) site ω one Y true z i j‖≤cash i j) →
  (∀ᶠ z:ℕ×ℕ in f.fuse,∀t i j,‖cutoff R a (fun _:I=>h) site ω one Y t z i j-
      submitted R W (fun _:I=>h) sale t z i j‖≤σ t i j ∧
      deposits R W (fun _:I=>h) sale t z i j≤old t i j) →
  0<η → K*max 0 (fee η (σ false+old false))≤1/2 →
  2*K*(max 0 (fee η (σ true+old true))+max 0 (fee η (σ false+old false))*(K*(∑i,∑j,cash i j)))≤price →
  ‖transition R h J P r s‖≤K*(∑i,∑j,cash i j) ∧ ∀ᶠ z:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),
    IsUnit (sale.frame false z).det ∧ ‖transition R h J P r s-(sale.frame false z)⁻¹*sale.frame true z‖≤price

theorem original:
    ∃K:ℝ,0<K ∧ ∀(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ→tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ→ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g),
    G.Simple → Coupling G g → Leading F J → (ℓ:Filter (ℕ×ℕ))≤f.fuse →
    ∃(C:ℝ)(k:ℕ),0<C ∧ ∀ᶠ t in trail,∀ E:ℝ,1≤E →
      Receives (f:=f) (S:=S) B h a R J ℓ (Γ.date t) t (t/E) ((C*E^k*K)*(C*E^k)) avoid:=by
  obtain ⟨K,kp,reference⟩:=WilsonOriginalPublicRelativeGramReporting.original B h a
  refine ⟨K,kp,?_⟩
  intro R f S F J ℓ avoid g Γ simple temp lead below
  obtain ⟨C,k,cp,priced⟩:=WilsonOriginalPublicRelativeGramOptical.original R F h J (named R B h) lead
  refine ⟨C,k,cp,?_⟩
  filter_upwards [reference R F J avoid Γ simple temp lead,priced] with t actual gates
  intro E ep'
  let r:=t/E
  let D:=(C*E^k*K)*(C*E^k)
  have dp:0≤D:=by dsimp [D]; positivity
  intro W s Y b sale cash σ old η price converges same rough earned ep stable paid
  let o:=fun _:Unit=>ports R avoid (pointsAt a) (Γ.date t) t
  let μ:=fun _:Unit=>(1:ℂ)
  have clear:∀m,μ m≠0→Extraction.Order.grid R.family (Γ.date t) (o m)∈generic 2:=fun _ _=>actual.1
  letI : DecidableEq (Glyph B h):=fun i j=>Classical.propDecidable (i=j)
  let M:=matrix R F a (fun _:I=>h) J (fun i=>named R B h i) r s (Γ.date t) o μ false
  let ref:=matrix R F a (fun _:I=>h) J (fun i=>named R B h i) t t (Γ.date t) o μ true
  let ref₀:=matrix R F a (fun _:I=>h) J (fun i=>named R B h i) t t (Γ.date t) o μ false
  have eq₀:ref=ref₀:=rfl
  have refRank:IsUnit ref.det:=by
    rw [eq₀]
    convert actual.2.1 using 1
    congr! 4
  have refPrice:‖ref⁻¹‖≤K:=by
    rw [eq₀]
    convert actual.2.2 using 1
    congr! 4
  have wide:=WilsonOriginalPublicRelativeGramWide.priced R F a h J (named R B h) r t (Γ.date t) o μ
    refRank refPrice (gates E ep').1 (gates E ep').2
  have rank:IsUnit M.det:=by convert wide.1 using 1; congr! 4
  have inv:‖M⁻¹‖≤D:=by convert wide.2 using 1; congr! 4
  have field:=WilsonOriginalPublicRelativeGramRough.original R F a h J (named R B h) r s (Γ.date t) o μ Y
    b converges same below clear cash rough dp rank inv
  have budget:2*D*(max 0 (fee η (σ true+old true))+max 0 (fee η (σ false+old false))*
      ‖transition R h J (named R B h) r s‖)≤price:=by
    calc
      _ ≤ 2*D*(max 0 (fee η (σ true+old true))+max 0 (fee η (σ false+old false))*(D*(∑i,∑j,cash i j))):=
        mul_le_mul_of_nonneg_left
          (add_le_add_right (mul_le_mul_of_nonneg_left field (le_max_left ..)) _) (by positivity)
      _ ≤ price:=paid
  have funded:=WilsonOriginalPublicRelativeGramSale.original R W F a h J (named R B h)
    r s (Γ.date t) o μ Y sale b converges same below clear σ old η ep earned rank D price inv stable budget
  refine ⟨field,?_⟩
  filter_upwards [funded] with z answer
  convert answer using 1 <;> congr! 8

end YM.Integration.WilsonOriginalPublicRelativeGramWideStation
