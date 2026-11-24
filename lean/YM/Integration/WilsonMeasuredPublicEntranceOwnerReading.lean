import YM.Integration.WilsonMeasuredPublicEntranceOwner
import YM.Integration.WilsonMeasuredCompanionTransport
import YM.Integration.WilsonOriginalOccupiedTransport
import YM.Integration.WilsonOriginalAlternativeHearing

/-! Read an actual signed hard owner together with all distinct ordinary
peers on the earlier physical flat. Both pointed readings retain the same
untouched original hard gas. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwnerReading
open Function MeasureTheory Lattice Wilson RG Source Labels Marker QuadraticLocal
open PhysicalNext PhysicalNext.Repeat Legato MergeProof.Accent
open WilsonOriginalDepositedHard WilsonMeasuredCoefficientTransport WilsonOriginalAlternativeHearing
open WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p f j : ℕ} {V T I : Type} [DecidableEq V] [Fintype V] [Countable I]
    {J : Census V} (W : Rep G (R.family.side f p)) (o : V→Site (R.family.side f p))
    (E : Lamps T I G W.p o J) (v : V) {d : ℕ} {F : Frame G d} (h : Coefficient F (R.family.side f p))
    {Y : Hol G} {κ M k α δ Λ C' z : ℝ} (fit : h.Format (o v) Y W)
    (fund : h.remBound (o v) W κ M) (rent : Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent k)
    (law : W.Lawful α C' Λ δ z) (w : V→ℝ) (wp : ∀i,0<w i)
    (bills : E.Paid w W.p.B W.p.supportExponent 1)
local notation "quiet" => (Hard.rent rent : Hard T W.p W.activities.forced W.activities.K o J)
local notation "raised" => joined (quiet) v h fit (fun _ => (1:ℂ))
local notation "G₀" => (⟨E,quiet⟩:Gallery T I o W J)
local notation "G₁" => (⟨E,raised⟩:Gallery T I o W J)

include fund law w wp bills in
theorem original (S : SectionData F) (x : T) (s : J.Mode) (jf : j≤f) :
    held R.family N p (fun U=>account h W U*WilsonMeasuredCompanionFace.peers E v s x U) jf 1 =
      (((R.family.path.rep N p j).eval 1:ℂ)⁻¹)*
        ((gust R.family.path N p f ((G₁).density x) j jf 1).part s-
         (gust R.family.path N p f ((G₀).density x) j jf 1).part s) := by
  classical
  obtain ⟨raw,gross,exactly,_⟩ := WilsonMeasuredPublicEntranceOwner.original v h fit fund rent E w wp bills x s S
  have b₀ := QuadraticLocal.Tariff.integrable J o w wp (G₀) x raw W.p.exponent_pos.le law
  have b₁ := QuadraticLocal.Tariff.integrable J o w wp (G₁) x gross W.p.exponent_pos.le law
  have split := WilsonMeasuredCompanionTransport.subtract R (N:=N)
    (fun U=>((G₁).density x U).part s) (fun U=>((G₀).density x U).part s)
    ((Poly.get s).integrable_comp b₁) ((Poly.get s).integrable_comp b₀) jf
  simp only [reading] at split
  simp only [held,Complex.real_smul,Complex.ofReal_inv]
  rw [funext exactly,split,←WilsonOriginalOccupiedTransport.projected R _ b₁ s jf,
    ←WilsonOriginalOccupiedTransport.projected R _ b₀ s jf,mul_sub]

end YM.Integration.WilsonMeasuredPublicEntranceOwnerReading
end
