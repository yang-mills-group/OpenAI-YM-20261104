import YM.Integration.WilsonOriginalPublicRelativeGramOuterAbsorption
import YM.Integration.WilsonOriginalPublicRelativeGramOuterScale
import YM.Integration.WilsonOriginalPublicPlantedGramFilms

/-! Genuine before-cutoff charge for the original outer arm on a compact reflected profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterSelf
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus Pert.Asymptotics

open Set Filter Function Lattice Wilson RG Source OPE Extraction Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramBookedHeads (source)
open RG17 Spec Table Climb XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open Labels Cells GapsContact.Stamps Trace.Terrace Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open WilsonThermometerUnitFilingFourPoolShell (radius)
open WilsonOriginalPublicRelativeGramFreePanel (pointsAt named)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (cutoff)
open WilsonAddressedPublicHomeCard (exponent)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee width)
open scoped Topology Classical BigOperators

open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonAddressedPublicPairPins (name)

open WilsonOriginalPublicRelativeGramOuterCards (actors)
open WilsonOriginalPublicPivotCross (detector old left right)
open WilsonOriginalPublicPivotReflected (sampled)
open WilsonOriginalPublicPlantedGramFilms (reflected pupil)
open WilsonPositionProgramPublicReflectedRead (lower)
open MS.Menus
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ → tower S)(Z:WilsonPrescription G)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
local notation "g" => wilson z


/-- One fixed-rank purchase before any aperture and order. The original
finite ensemble and the independently normalized finite torus are both explicit. -/
theorem original (simple : G.Simple)(bliss : Bliss F ℓ z H)(lead : Leading F J)
    (guard : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (bank : PostT R.family.path.levels)(slow : WilsonWindowReportingPace.Slow R.kit)
    {h : ℕ}{I : Type}[Fintype I](v : I → RG17.Free R.family h)(T : ℕ)
    {ms : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {pos : Prescription (Press.portDeck G)}{dial : Bool}(matched : Main.Match Z simple ms pos dial)
    (B : Deck G)(axis : Axis){L : Type}[Fintype L](mass : ℝ)(mp : 0 < mass) :
    ∃C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (Dlog : ℕ)(Jlog : ℝ)(q : ℕ),∃j₀ : ℕ,∃ρ : ℝ,0 < ρ ∧
    ∀{τ : ℝ}, 0 < τ → ∀ᶠs in trail,
    ∀{D : ℕ}(seats : h  ≤  D)(book : Book F (l:=ℓ) H z D T s), Housed F book →
    ∀(site : ℕ)(u : L → Fin 2 → Cover)(μ : L → ℂ),
    (∀b,‖R.family.S.gridPoint site (u b 0-u b 1)‖  ≤  1) →
    (∀b,τ*s  ≤  ‖R.family.S.gridPoint site (u b 0)-R.family.S.gridPoint site (u b 1)‖) →
    ∑b,μ b=1 → ∑b,‖μ b‖  ≤  mass →
    ∀ᶠp : ℕ×ℕ in f.fuse,∀j:I,∀i≥j₀,(i:ℝ)  ≤  Jlog*(-Real.log (g s))^Dlog →
    ∀{cap : ℕ}(_binder : Handoff.Directory Z i cap),Handoff.Directory.budget G 2 h+q  ≤  cap →
    ∀(X : L → Sample 2),(∀l,(X l).F=Z.run.step i) →
    (∀l,welcome (X l) ∧ dist (familiar (X l)) (lower axis) < ρ) →
    ∀(ξ : ℝ),|ξ|  ≤  8*g s →
    ∀(d : Fin 2 → ℕ)(seed : (i : Fin 2) → (R.family.labels.level (d i)).Coeff)
      (a : Glyph B h → ℂ),
    let physical := cutoff R axis (fun _:I=>h) site u μ (fun _=>actors R F J Z book seats v) false p j j
    let H₀ := detector Z.scheme X μ q ξ
    let A := reflected Z axis i (β:=B) (d:=h)
    let E := pupil Z i (β:=B) (d:=h)
    let U := left R Z.scheme d seed a A
    let V := right R Z.scheme d seed a E
    ‖sampled R Z.scheme d seed X μ Finset.univ q ξ-physical‖  ≤  1 →
    ‖((∑l,star (a l)*H₀ (A l*V))+(∑l,a l*H₀ (U*E l)))+
      (old R Z.scheme d seed X μ q ξ+H₀ (U*V))‖  ≤  (k/8)*(1+‖a‖)^2 →
    ‖a‖*(g s)^(exponent T h)  ≤  C := by
  classical
  obtain ⟨M,m1,baseline⟩ := WilsonOriginalPublicRelativeGramOuterCards.original
    R F J Z simple bliss lead guard bank slow v T
  obtain ⟨k,δ,kp,dp,buy⟩ := WilsonOriginalPublicRelativeGramOuterAbsorption.original
    axis (id : Glyph B h → Glyph B h) injective_id
  let gain := max 1 ((mass+k/4+5)/(k/2))
  have mg : 0 < gain := zero_lt_one.trans_le (le_max_left ..)
  refine ⟨gain*M,k,mul_pos mg (zero_lt_one.trans_le m1),kp,?_⟩
  intro Dlog Jlog q
  let link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨j₀,ρ,hp,printed⟩ := WilsonOriginalPublicPlantedGramFilms.original
    (L:=L) Z matched axis (id : Glyph B h → Glyph B h) δ mass dp mp trail
    link.positive (link.conforms simple) Dlog Jlog q
  refine ⟨j₀,ρ,hp,?_⟩
  intro τ tp
  filter_upwards [baseline tp,printed,link.positive,(link.conforms simple).eventually
    (gt_mem_nhds zero_lt_one)] with s charged report gp small
  intro D seats book housed site u μ room shape one total
  filter_upwards [charged seats book housed site u μ room shape] with p wages
  intro j i late roof cap binder levels X fold near ξ xp d seed a physical H₀ A E U V reception scar
  let money := (g s)^(exponent T h)
  have hot : 0 < money := pow_pos gp _
  have fitted : money  ≤  1 := pow_le_one₀ gp.le small.le
  have bound : 1  ≤  M/money := (le_div_iff₀ hot).mpr (by simpa using fitted.trans m1)
  have diag := (wages j axis).trans (mul_le_mul_of_nonneg_right total (sq_nonneg _))
  have done := buy R Z.scheme d seed X μ q ξ physical a A E mass (M/money) mp.le bound
    (report i late roof binder levels X μ fold near one total ξ xp) diag reception scar
  have cost : ‖a‖  ≤  (gain*M)/money := done.trans_eq (by change gain*(M/money)=(gain*M)/money;ring)
  exact (le_div_iff₀ hot).mp cost

end YM.Integration.WilsonOriginalPublicRelativeGramOuterSelf
end
