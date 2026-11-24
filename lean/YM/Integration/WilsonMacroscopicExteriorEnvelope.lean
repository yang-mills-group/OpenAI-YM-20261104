import YM.Integration.WilsonMacroscopicVacuumFactor
import YM.Integration.WilsonReportMomentEnvelope

/-! A single radius for every running input. The fixed external fields
enter through their own true unit response, without a spurious r-scaled
compactness condition on their positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicExteriorEnvelope
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book}
  {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ} (source : FundedOriginalProperties.{u} hG b W)
  (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
  (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V)
  (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (J : ℝ → PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d)
  {n : ℕ} (d : Caps n) {E : Type} [Fintype E] {e : E→ℕ} (w : Labels V e)
  {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {δ : ℝ} (hδ : 0<δ)
  {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g)
include hG W source pace hB fac Q leading paid hk sep hδ hg

theorem signed (p : ℕ) {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∃ c : ℝ,0≤c ∧ ∀ᶠ r in Trace.Pilot.trail,∀ x∈K,∀ y : E→E4,ClearOf 0 y δ →
      ∀ t : Viewers F,∀ v : (i:Fin n)→Free R.family (d i),
        let ins : Labels V d := fun i=>J r (d i) (v i)
        let ext := upon (spectator F t) 0 0 y w (V.unit 0)
        ‖whole (spectator F t) (RG17.posed r x) ins y w - V.classMoment V d (r • x) ins * ext‖ ≤
          c*(ε*g r^p*r^(1-σ)*(1+‖ext‖))*(∏ i,‖v i‖) := by
  let P (i : Fin n) := Free R.family (d i)
  let coordsL (a : Code P) (i : Fin n) := ((Module.finBasis ℂ (P i)).coord (a i)).toContinuousLinearMap
  let size (a : Code P) := ∏ i,‖coordsL a i‖
  have sn (a : Code P) : 0 ≤ size a := prod_nonneg fun i _=>ContinuousLinearMap.opNorm_nonneg _
  have price (a : Code P) (v : (i:Fin n)→P i) : ‖coords P a v‖ ≤ size a*∏ i,‖v i‖ := by
    unfold coords size;rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>(coordsL a i).le_opNorm _)
  obtain ⟨M,η,hM,hη,room⟩ := RG17.roomCosts hk sep
  have all := eventually_all.mpr fun a : Code P=>WilsonMacroscopicVacuumFactor.original hG W source pace hB F fac Q J leading paid (combination P a) w hM hη hδ hg p hσ hε
  refine ⟨∑ a : Code P,size a,sum_nonneg (fun a _=>sn a),?_⟩
  filter_upwards [all,RG17.positiveLength,hg.positive] with r rows rp gp x hx y clear t v
  let u := upon (spectator F t) 0 0 y w (V.unit 0)
  let Cμ := ε*g r^p*r^(1-σ)*(1+‖u‖)
  have C₀ : 0≤Cμ := mul_nonneg (mul_nonneg (mul_nonneg hε.le (pow_nonneg gp.le _)) (Real.rpow_nonneg rp.le _)) (by positivity)
  let full := (sectionLabels (d:=Sum.elim d e) w (Orbits.moment (spectator F t) (beside (RG17.posed r x) y))).compLinearMap (fun i=>(J r (d i)).toLinearMap)
  let near := (V.classMoment V d (r • x)).compLinearMap (fun i=>(J r (d i)).toLinearMap)
  let m := full-u • near
  have obs (v : (i:Fin n)→P i) : m v=whole (spectator F t) (RG17.posed r x) (fun i=>J r (d i) (v i)) y w - V.classMoment V d (r • x) (fun i=>J r (d i) (v i))*u := by
    change sectionLabels (d:=Sum.elim d e) w (Orbits.moment (spectator F t) (beside (RG17.posed r x) y)) (fun i=>J r (d i) (v i)) -u*_ = _
    rw [sectionLabels_apply,mul_comm u];rfl
  have hconf := Work.A05.smul_conf rp (sep hx)
  have hrow (a : Code P) : ‖m (combination P a)‖≤Cμ := by
    let words (i : Fin n) : V.Tag := ⟨d i,J r (d i) (combination P a i)⟩
    have q := rows a (RG17.posed r x) 0 y (room r rp x hx) hconf clear t
    have usual := PhysMS.point_moment F none words hconf
    simp only [unselected_view] at usual
    rw [obs]
    change ‖_ - V.useAt V (r • x) words*u‖≤Cμ
    rw [usual];exact q
  let v₀ := ∏ i,‖v i‖
  have vp : 0≤v₀ := prod_nonneg fun _ _=>norm_nonneg _
  change ‖_ - _*u‖≤(∑ a : Code P,size a)*Cμ*v₀
  rw [←obs,basis_tuple P v m]
  calc
    _ ≤ ∑ a : Code P,‖coords P a v * m (combination P a)‖ := norm_sum_le ..
    _ ≤ ∑ a : Code P,size a*(Cμ*v₀) := sum_le_sum fun a _=>by
      rw [norm_mul]
      exact (mul_le_mul (price a v) (hrow a) (norm_nonneg _) (mul_nonneg (sn a) vp)).trans_eq (by ring)
    _ = (∑ a : Code P,size a)*(Cμ*v₀) := (sum_mul ..).symm
    _ = _ := (mul_assoc ..).symm

theorem amplitude : ∃ D : ℝ,0≤D ∧ ∀ᶠ r in Trace.Pilot.trail,∀ x∈K,
    ∀ y : E→E4,ClearOf 0 y δ → ∀ t : Viewers F,∀ v : (i:Fin n)→Free R.family (d i),
    let ext := upon (spectator F t) 0 0 y w (V.unit 0)
    ‖whole (spectator F t) (RG17.posed r x) (fun i=>J r (d i) (v i)) y w‖ ≤
      D*(1+‖ext‖)*(∏ i,‖v i‖) := by
  obtain ⟨c,hc,cmp⟩:= signed hG W source pace hB F fac Q J leading paid d w hk sep hδ hg 0 (by norm_num : 0<(1/2:ℝ)) zero_lt_one
  obtain ⟨M,hM,cap⟩:= WilsonReportMomentEnvelope.purchased F J leading paid d K hk sep
  refine ⟨c+M,add_nonneg hc hM.le,?_⟩
  filter_upwards [cmp,cap,RG17.positiveLength,(show ∀ᶠ r in RG17.home,r≤(1:ℝ) from nhdsWithin_le_nhds (ge_mem_nhds zero_lt_one))] with r obs grant rp r1 x hx y clear t v
  let ins : Labels V d := fun i=>J r (d i) (v i)
  let z := V.classMoment V d (r • x) ins
  let a := whole (spectator F t) (RG17.posed r x) ins y w
  let u := upon (spectator F t) 0 0 y w (V.unit 0)
  let v₀ := ∏ i,‖v i‖
  have vn : 0≤v₀ := prod_nonneg fun i _=>norm_nonneg _
  have bb := obs x hx y clear t v
  simp only [pow_zero,mul_one,one_mul] at bb
  have main : ‖a-z*u‖≤c*(1+‖u‖)*v₀ := bb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (by positivity) (Real.rpow_le_one rp.le r1 (by norm_num))) hc) vn)
  have single : ‖z*u‖≤M*(1+‖u‖)*v₀ := by
    rw [norm_mul]
    have charge := mul_le_mul (grant x hx v) (le_add_of_nonneg_left zero_le_one : ‖u‖≤1+‖u‖) (norm_nonneg _) (mul_nonneg hM.le vn)
    exact charge.trans_eq (by ring)
  change ‖a‖≤(c+M)*(1+‖u‖)*v₀
  exact (norm_le_norm_sub_add a (z*u)).trans ((add_le_add main single).trans_eq (by ring))

end YM.Integration.WilsonMacroscopicExteriorEnvelope
