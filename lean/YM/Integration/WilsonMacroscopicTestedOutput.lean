import YM.Integration.WilsonMacroscopicDetector

/-! The original RG17 tested-output receipt on the selected physical
experiment. Its emitted Wilson field is a representative of the estimate
from full product measurements. It is chosen before the family of exterior
tests used to check the signed discrepancy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicTestedOutput
open Function Filter Finset Set MeasureTheory Extraction Table
open Next.Rank OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonMacroscopicDetector
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T)
    {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
    (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0 < B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F A (J r) d) :
    ∃ L : Layout F, L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B ∧
    ∀ {n : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
      {K : Set (Points n)}, IsCompact K → K ⊆ conf n → ∀ {g : ℝ → ℝ}, Trace.Pilot.Coupling G g →
    ∀ H : ℕ, ∃ (M : Test n → ℝ → R.family.label H) (p : ℕ),
    (∀ᶠ r in Trace.Pilot.trail, ∀ ψ : Test n,
      let x := fromProducts F H (fun i=>J r (d i) (v i)) r ψ
      master L H r (M ψ r)=x ∧ mass R.family H (L.shift H r (M ψ r)) ≤
        R.family.path.levels.clock.hatBeta (L.level r)^p*‖(J r H).symm x‖) ∧
    ∀ Y : Finset (RG17.External R.family V),
      RG17.TestedOutput (Pier.Lair.tender F L J) (d:=d) (fun i=>Sum.inr (v i)) H Y K M := by
  obtain ⟨L,level,_,buy⟩ := WilsonMacroscopicExteriorMeasurement.located hG W source pace hB F fac Q J leading paid
  refine ⟨L,level,?_⟩
  intro n d v K compact apart g hg H
  let Z := Pier.Lair.tender F L J
  let u (r : ℝ) : Labels V d := fun i=>J r (d i) (v i)
  let x (ψ : Test n) (r : ℝ) := fromProducts F H (u r) r ψ
  obtain ⟨p,hp⟩ := (buy H).affordability
  let cert (ψ : Test n) (r : ℝ) (v : R.family.label H) := master L H r v=x ψ r ∧
    mass R.family H (L.shift H r v) ≤ R.family.path.levels.clock.hatBeta (L.level r)^p*‖(J r H).symm (x ψ r)‖
  let M (ψ : Test n) (r : ℝ) := if h : ∃ v, cert ψ r v then h.choose else 0
  have sales : ∀ᶠ r in Trace.Pilot.trail, ∀ ψ : Test n, cert ψ r (M ψ r) := by
    filter_upwards [hp] with r atRadius ψ
    obtain ⟨z,amount,same⟩ := atRadius.1 ((J r H).symm (x ψ r))
    change master L H r z=J r H ((J r H).symm (x ψ r)) at same
    have existsRow : ∃ z,cert ψ r z := ⟨z,by simpa using same,amount⟩
    dsimp only [M]
    rw [dif_pos existsRow]
    exact existsRow.choose_spec
  refine ⟨M,p,sales,?_⟩
  intro Y
  let rent (X : RG17.External R.family V) := ∫ z : Points (X.n+1), ‖X.test z‖
  let price (X : RG17.External R.family V) := rent X + ‖(X.charge F H).toContinuousLinearMap‖*fee F H
  have fpos : 0 ≤ fee F H := mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (Finset.sum_nonneg fun _ _=>integral_nonneg fun _=>norm_nonneg _)
  have ppos (X : RG17.External R.family V) : 0 ≤ price X := add_nonneg (integral_nonneg fun _=>norm_nonneg _)
    (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) fpos)
  have half : 0 < (1/2:ℝ) := by norm_num
  have tested := (eventually_all_finset Y).mpr fun X _=>
    WilsonMacroscopicExteriorMeasurement.signed hG W source pace hB F fac Q J leading paid d v X compact apart hg H 0 half zero_lt_one
  have det := WilsonMacroscopicDetector.original hG W source pace hB F fac Q J leading paid d v compact apart hg H 0 half zero_lt_one
  refine ⟨1/2,∑ X∈Y,price X,0,half,Finset.sum_nonneg fun X _=>ppos X,?_⟩
  filter_upwards [sales,tested,det,RG17.positiveLength] with r actual measures decoder rp
  intro X hX ψ support b invoice
  let m := ∫ z : Points n, ‖ψ z‖
  let P := RG17.basket Q H (u r) r ψ
  let a := r^((H:ℝ)+1/2)
  have ap : 0 ≤ a := Real.rpow_nonneg rp.le _
  have mp : 0 ≤ m := integral_nonneg fun _=>norm_nonneg _
  have eqPower : (H:ℝ)+1-1/2=(H:ℝ)+1/2 := by ring
  have read : ‖RG17.appeared F (u r) X r ψ-X.charge F H P‖ ≤ a*rent X*m := by
    simpa only [pow_zero,mul_one,one_mul,eqPower] using (measures X hX ψ support)
  have estimate : ‖x ψ r-P‖ ≤ fee F H*a*m := by
    simpa only [pow_zero,mul_one,one_mul,eqPower] using (decoder ψ support)
  change ‖RG17.appeared F (u r) X r ψ-X.charge F H (master L H r (M ψ r))‖ ≤ (∑ E∈Y,price E)*a*b
  rw [(actual ψ).1]
  have charge : ‖X.charge F H P-X.charge F H (x ψ r)‖ ≤
      ‖(X.charge F H).toContinuousLinearMap‖*(fee F H*a*m) := by
    rw [← map_sub]
    apply ((X.charge F H).toContinuousLinearMap.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg _)
    rw [norm_sub_rev]
    exact estimate
  have pin : price X ≤ ∑ E∈Y,price E := Finset.single_le_sum (fun E _=>ppos E) hX
  calc
    _ ≤ ‖RG17.appeared F (u r) X r ψ-X.charge F H P‖+‖X.charge F H P-X.charge F H (x ψ r)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ a*rent X*m+‖(X.charge F H).toContinuousLinearMap‖*(fee F H*a*m) := add_le_add read charge
    _ = price X*a*m := by dsimp only [price]; ring
    _ ≤ (∑ E∈Y,price E)*a*b := mul_le_mul (mul_le_mul_of_nonneg_right pin ap) invoice.norm mp
      (mul_nonneg (Finset.sum_nonneg fun E _=>ppos E) ap)

end YM.Integration.WilsonMacroscopicTestedOutput
