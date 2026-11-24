import YM.Integration.WilsonThermometerWeakWardPair
import YM.Integration.WilsonThermometerWeakProjectedSolve

/-! Two actual reflected chambers hear the finite Ward quotient. The right arm,
the funded original prior, and the signed linear responses are fixed in the
entire determinant and its solve. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardSolve
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat Legato Bandage Cells Next.UVStress RG05Readout RG05Readout.Address
open WilsonOffsetReportingProducts WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open WilsonThermometerRelativeWard WilsonThermometerWeakEquationCost WilsonThermometerWeakWardReading
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
variable (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
include W portfolio issued

theorem original (simple:G.Simple) (D:Deck G) (d:ℕ) : ∃ radius:ℕ,∀ᶠ k:ℕ in atTop,∀ᶠ N:ℕ in atTop,
    ∃ h:k≤N,∀ (p m:ℕ) (prior:m≤k) (o:Site ((C).side N p)),
    let T:=center (C).S p (prior.trans h) 0
    ∀ (v u:Site ((C).side m p)),v≠u → o∈T.margin v (3*span (C).S h p) →
    ∀ (X Z:Glyph D d→(Config G ((C).side N p)→ℂ)) (test:∀i,Continuous (X i))
      (right:ℝ), (∀i,LocalOn (Mark.Outer radius o) (X i)) → (∀i,T.copy u (Z i)=X i) →
      (∀i,Interior (T.chamber 0) (Z i)) → (∀i,T.rootTest ((C).beta N p) (Z i)≤right) →
    ∀ (sites:∀j,Bud C p j) (B:ℕ→ℕ→ℝ) (A:Sight C d p) (r:Emblems C d),
      Enrolled R.makes R.doors B k N p d sites A r →
    ∀ (E:(Glyph D d→ℂ) →ₗ[ℂ] (C).label d) (y:(Glyph D d→ℂ)→Palette C d)
      (Y:ℝ), (∀t,E t=column R (p:=p) r h (y t)) → (∀t,size (y t)≤Y*‖t‖) →
    ∀ (M:Matrix (Glyph D d) (Glyph D d) ℂ), (∀ t i, read R d N p o (X i) (test i) (E t)=(t ᵥ* M) i) →
    IsUnit M → ∀ (I:ℝ), 0≤I → (∀i j,‖M⁻¹ i j‖≤I) →
    ∀ (x:(C).label d) (Q:ℝ), 0≤Q → (∀i,‖read R d N p o (X i) (test i) x‖≤Q) →
    let τ:=2*Real.exp (-(3/128:ℝ)*(C).S.scale N)*right
    let K:ℝ:=(Fintype.card (Glyph D d):ℝ)*I
    0≤right → 2*K*(τ*Y)≤1 →
    ∃t:Glyph D d→ℂ, b.step d (N,p) (E t)=b.step d (N,p) x ∧
      ‖t‖≤2*K*(Q+τ*(Fintype.card ((C).labels.level d).Index*‖x‖)):=by
  obtain ⟨radius,funding⟩:=WilsonThermometerWeakWardPair.original R V W P b portfolio issued simple d
  refine ⟨radius,?_⟩
  filter_upwards [funding] with k next
  filter_upwards [next] with N bought
  obtain ⟨h,root⟩:=bought
  refine ⟨h,?_⟩
  intro p m prior o T v u apart left X Z test right distal posted clears budget sites B A r intake
    E y Y loans tariff M reads inv I hI cost x Q good mixed τ K goodR afford
  let L:=LinearMap.pi fun i=>read R d N p o (X i) (test i)
  have invoice (w:(C).label d) (t:Glyph D d→ℂ) (eq:b.step d (N,p) (E t)=b.step d (N,p) w):
      ‖L (E t)-L w‖≤τ*(Fintype.card ((C).labels.level d).Index*‖w‖+Y*‖t‖):=by
    have base:0≤Fintype.card ((C).labels.level d).Index*‖w‖+size (y t):=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (size_ge _)
    have expGood:0≤Real.exp (-(3/128:ℝ)*(C).S.scale N):=(Real.exp_pos _).le
    apply (pi_norm_le_iff_of_nonneg _).2
    · intro i
      have cell:=root p m prior v u apart o left (Z i) (X i) (test i) (distal i) (posted i) (clears i)
        sites B A r intake w (y t) (by rw [←loans];exact eq.symm)
      rw [←loans t,norm_sub_rev] at cell
      exact cell.trans <| calc
        _ ≤ (2*(Fintype.card ((C).labels.level d).Index*‖w‖+size (y t)))*
            Real.exp (-(3/128:ℝ)*(C).S.scale N)*right:=
          mul_le_mul_of_nonneg_left (budget i) (mul_nonneg (mul_nonneg (by norm_num) base) expGood)
        _ = τ*(Fintype.card ((C).labels.level d).Index*‖w‖+size (y t)):=by dsimp only [τ];ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add_right (tariff t) _) (by dsimp only [τ];positivity)
    · apply mul_nonneg (by dsimp only [τ];positivity)
      exact base.trans (add_le_add_right (tariff t) _)
  apply WilsonThermometerWeakProjectedSolve.original C D d V W b issued (N,p) E L M
      (fun t=>funext (reads t)) inv I hI cost x τ Y _ Q
  · exact (pi_norm_le_iff_of_nonneg good).2 mixed
  · intro t null
    have small:=invoice 0 t (by rwa [map_zero])
    simpa [mul_assoc] using small
  · exact invoice x
  · exact afford

end YM.Integration.WilsonThermometerWeakWardSolve
end
