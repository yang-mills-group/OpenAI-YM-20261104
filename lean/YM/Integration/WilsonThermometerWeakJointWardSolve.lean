import YM.Integration.WilsonThermometerWeakJointWardMenu

/-! The equation-ideal deduction for the two independent Wilson sites uses
the very same original signed Gram before the common lattice translation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakJointWardSolve
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat Legato Bandage Cells Next.UVStress RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerWeakPanelBorn WilsonThermometerOwnOffsetField
open Push.RelayDifference
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy
open WilsonThermometerWeakJointWardMenu (lodged)
open WilsonThermometerWeakWardRows (gram)
open WilsonThermometerWeakFourLinearRows (stencil entrance)
open WilsonThermometerWeakEquationCost (column)
open WilsonThermometerWeakWardReading (read)
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
variable (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))
include W portfolio issued

theorem original (simple:G.Simple) (D:Deck G) (d:ℕ) : ∃radius:ℕ,∀ᶠ k:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃hk:k≤N,
    ∀(p:ℕ)(loc:Fin 2→Site ((C).side N p))(r:Fin 2→Emblems C d)(u:Fin 2→Glyph D d→(C).label d)
      (S F I:ℝ),0≤S → 0≤F → 0≤I →
    lodged R hk loc (r 1) (u 1) S radius → (∀i j,((C).labels.level d).coeffSize (u i j)≤F) →
    ∀(sites:∀j,Bud C p j)(B:ℕ→ℕ→ℝ)(data:Sight C d p),Enrolled R.makes R.doors B k N p d sites data (r 0) →
    let M:=gram R loc r hk u
    IsUnit M → (∀i j,‖M⁻¹ i j‖≤I) →
    ∀(x:(C).label d)(Q:ℝ),0≤Q →
    (∀i,‖moment ((C).beta N p) (fun U=>(C).O N p x (loc 0) U*arm R (r 1) hk (loc 1) (u 1 i) U)‖≤Q) →
    let n:ℝ:=Fintype.card (Glyph D d)
    let τ:=2*Real.exp (-(3/128:ℝ)*(C).S.scale N)*(S*F)
    2*(n*I)*(τ*(‖((C).S.a k:ℂ)^d‖*(n*F)))≤1 →
    ∃y:Palette C d,b.step d (N,p) (entrance R (p:=p) (r 0) hk y)=b.step d (N,p) x ∧
      size y≤(2*(n*I)*(Q+τ*(Fintype.card ((C).labels.level d).Index*‖x‖)))*(n*F):=by
  obtain ⟨radius,solve⟩:=WilsonThermometerWeakWardSolve.original R V W P b portfolio issued simple D d
  refine ⟨radius,?_⟩
  filter_upwards [solve] with k opened
  filter_upwards [opened] with N won
  obtain ⟨hk,law⟩:=won
  refine ⟨hk,?_⟩
  intro p loc r u S F I hS hF hI cells rent sites B data enrolled M stable inv x Q hQ mixed n τ afford
  obtain ⟨m,hm,t,c₀,c₁,apart,left,arms⟩:=cells
  let T:=center (C).S p (hm.trans hk) 0
  let X:=fun a=>arm R (r 1) hk (loc 1+t) (u 1 a)
  have ct (a:Glyph D d):Continuous (X a):=WilsonThermometerWeakWardRows.continuous R ..
  choose Z inside cash same using fun a=>(arms a).2
  have cap (a:Glyph D d):T.rootTest ((C).beta N p) (Z a)≤S*F:=
    (cash a).trans (mul_le_mul_of_nonneg_left (rent 1 a) hS)
  let E:=WilsonThermometerWeakFourLinearRows.panel R (p:=p) (r 0) hk (u 0)
  let raw (v:Glyph D d→ℂ):=stencil R (u 0) v
  let shift:ℂ:=((C).S.a k:ℂ)^d
  let scaled (v:Glyph D d→ℂ):=shift • raw v
  have exact_at (v:Glyph D d→ℂ):E v=column R (p:=p) (r 0) hk (scaled v):=by
    change shift • ((C).factory d N p).terminal (finer (r 0) hk (raw v) (primaryLetter d)) =
      ((C).factory d N p).terminal (finer (r 0) hk (shift • raw v) (primaryLetter d))
    rw [map_smul,Pi.smul_apply]
    exact (((C).factory d N p).terminal.map_smul shift _).symm
  have sumCap:∑i,((C).labels.level d).coeffSize (u 0 i)≤n*F:=by
    calc _≤∑_:Glyph D d,F:=Finset.sum_le_sum fun i _=>rent 0 i
         _=n*F:=by simp [n]
  have rawCap (v:Glyph D d→ℂ):size (raw v)≤‖v‖*(n*F):=
    (WilsonThermometerWeakFourLinearRows.tariff R (u 0) v).trans (mul_le_mul_of_nonneg_left sumCap (norm_nonneg _))
  have paid (v:Glyph D d→ℂ):size (scaled v)≤(‖shift‖*(n*F))*‖v‖:=by
    unfold scaled
    rw [size_smul,mul_assoc,mul_comm (n*F)]
    exact mul_le_mul_of_nonneg_left (rawCap v) (norm_nonneg _)
  have readM (v:Glyph D d→ℂ) (i:Glyph D d):read R d N p (loc 0+t) (X i) (ct i) (E v)=(v ᵥ* M) i:=
    WilsonThermometerWeakWardRows.shifted R loc t r hk u v i
  have cross (i:Glyph D d):‖read R d N p (loc 0+t) (X i) (ct i) x‖≤Q:=by
    rw [show read R d N p (loc 0+t) (X i) (ct i) x = _ from
      WilsonThermometerWeakWardRows.translated R loc t (r 1) hk (u 1 i) x]
    exact mixed i
  obtain ⟨v,hit,price⟩:=law p m hm (loc 0+t) c₀ c₁ apart left X Z ct (S*F)
    (fun i=>(arms i).1) same inside cap sites B data (r 0) enrolled E scaled (‖shift‖*(n*F))
    exact_at paid M readM stable I hI inv x Q hQ cross (mul_nonneg hS hF) afford
  exact ⟨raw v,hit,(rawCap v).trans (mul_le_mul_of_nonneg_right price (mul_nonneg (Nat.cast_nonneg _) hF))⟩

end YM.Integration.WilsonThermometerWeakJointWardSolve
end
