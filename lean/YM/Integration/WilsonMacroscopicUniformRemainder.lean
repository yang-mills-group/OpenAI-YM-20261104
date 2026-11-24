import YM.Integration.WilsonMacroscopicPrescribedInputs
import YM.Integration.WilsonReportMomentEnvelope

/-! The physical macroscopic OPE remainder is uniform in the running
normalized input fields.  Keep its full spatial order after replacing a
slot by an independently bounded promoted derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicUniformRemainder
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {V : Table R.family.book} {n : ℕ} {d : Caps n} {E : Type} [Fintype E] {e : E→ℕ}

def response (F : Spec.Final R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (H : ℕ) (x : Fin n→E4) (y : E→E4) (w : Labels V e) (t : Viewers F) :
    MultilinearMap ℂ (fun i=>V.Field (d i)) ℂ :=
  sectionLabels (d:=Sum.elim d e) w (Orbits.moment (spectator F t) (beside x y)) -
    ∑ j : Fin (H+1),(upon (spectator F t) j.1 0 y w).compMultilinearMap (Q.fresh j.1 x 0)

theorem read (F : Spec.Final R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (H : ℕ) (x : Fin n→E4)
    (v : Labels V d) (y : E→E4) (w : Labels V e) (t : Viewers F) : response F Q H x y w t v=formula F Q x 0 v y w H t := by
  have actual := tested_fields F Q x 0 v y w t H
  unfold formula;rw [←actual];unfold balance
  let rows (j : Fin (H+1)) : MultilinearMap ℂ (fun i=>V.Field (d i)) ℂ := (upon (spectator F t) j.1 0 y w).compMultilinearMap (Q.fresh j.1 x 0)
  let full := sectionLabels (d:=Sum.elim d e) w (Orbits.moment (spectator F t) (beside x y))
  have seen : full v=whole (spectator F t) x v y w := sectionLabels_apply ..
  change full v-(∑ j,rows j) v=_
  rw [seen,_root_.sum_apply];rfl

private theorem frame (d : Caps n) : ∃ c : ℝ, 0≤c ∧
    ∀ m : MultilinearMap ℂ (fun i=>Free R.family (d i)) ℂ,∀ b : ℝ,
    (∀ a : Code (fun i=>Free R.family (d i)),‖m (combination _ a)‖≤b) → ∀ v,‖m v‖≤c*b*(∏ i,‖v i‖) := by
  let P (i : Fin n) := Free R.family (d i)
  let coordinates (a : Code P) (i : Fin n) := ((Module.finBasis ℂ (P i)).coord (a i)).toContinuousLinearMap
  let size (a : Code P) := ∏ i,‖coordinates a i‖
  have sn (a : Code P) : 0 ≤ size a := prod_nonneg fun _ _=>ContinuousLinearMap.opNorm_nonneg _
  have invoice (a : Code P) (v : (i:Fin n)→P i) : ‖coords P a v‖ ≤ size a*∏ i,‖v i‖ := by
    unfold coords size;rw [norm_prod,←prod_mul_distrib]
    exact prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>(coordinates a i).le_opNorm _)
  refine ⟨∑ a : Code P,size a,sum_nonneg (fun a _=>sn a),?_⟩
  intro m b row v
  let v₀ := ∏ i,‖v i‖
  have vn : 0≤v₀ := prod_nonneg fun i _=>norm_nonneg _
  rw [basis_tuple P v m]
  calc
    _ ≤ ∑ a : Code P, ‖coords P a v*m (combination P a)‖ := norm_sum_le ..
    _ ≤ ∑ a : Code P,size a*(b*v₀) := sum_le_sum fun a _=>by
      rw [norm_mul];exact (mul_le_mul (invoice a v) (row a) (norm_nonneg _) (mul_nonneg (sn a) vn)).trans_eq (by ring)
    _ = (∑ a : Code P,size a)*(b*v₀) := (sum_mul ..).symm
    _ = _ := (mul_assoc ..).symm

theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {b : ℝ}
    (source : FundedOriginalProperties.{u} hG b W) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (F : Spec.Final R.family f V) (fac : OPE.Facilities R.family f V) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ→PhysMS.tower V) (leading : PhysMS.Leading F J) {A : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F A (J r) d) (d : Caps n) (w : Labels V e)
    {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) {δ : ℝ} (hδ : 0<δ) {g : ℝ→ℝ} (hg : Trace.Pilot.Coupling G g)
    (H q : ℕ) {σ ε : ℝ} (hσ : 0<σ) (hε : 0<ε) :
    ∀ᶠ r in RG17.home,∀ x∈K,∀ y : E→E4,ClearOf 0 y δ → ∀ t : Viewers F,∀ v : (i:Fin n)→Free R.family (d i),
      ‖formula F Q (RG17.posed r x) 0 (fun i=>J r (d i) (v i)) y w H t‖≤ ε*g r^q*r^((H:ℝ)+1-σ)*(∏ i,‖v i‖) := by
  let P (i : Fin n) := Free R.family (d i)
  obtain ⟨total,tn,contract⟩ := frame (R:=R) d
  have tn' : 0<total+1 := by linarith only [tn]
  obtain ⟨M,η,hM,hη,room⟩ := RG17.roomCosts hk sep
  have all := eventually_all.mpr fun a : Code P=> WilsonMacroscopicPrescribedInputs.original hG W source pace hB F fac Q J leading paid d (combination P a) w hM hη hδ hg H q hσ (div_pos hε tn')
  filter_upwards [all,RG17.positiveLength,hg.positive] with r terms rp gp x hx y clear t v
  let m := (response F Q H (RG17.posed r x) y w t).compLinearMap (fun i=>(J r (d i)).toLinearMap)
  let b := g r^q*r^((H:ℝ)+1-σ)
  have bn : 0≤b := mul_nonneg (pow_nonneg gp.le _) (Real.rpow_nonneg rp.le _)
  let c := (ε/(total+1))*b
  let v₀ := ∏ i,‖v i‖
  have vn : 0≤v₀ := prod_nonneg fun i _=>norm_nonneg _
  have obs (z : (i:Fin n)→P i) : m z=formula F Q (RG17.posed r x) 0 (fun i=>J r (d i) (z i)) y w H t :=
    read F Q H (RG17.posed r x) (fun i=>J r (d i) (z i)) y w t
  have row (a : Code P) : ‖m (combination P a)‖≤c := by
    rw [obs];exact (terms a _ _ y (room r rp x hx) clear t).trans_eq (mul_assoc ..)
  have coupon : total*(ε/(total+1))≤ε := by
    rw [←mul_div_assoc,div_le_iff₀ tn'];nlinarith only [hε]
  rw [←obs]
  calc
    _ ≤ total*c*v₀ := contract m c row v
    _ = (total*(ε/(total+1)))*b*v₀ := by dsimp only [c];ring
    _ ≤ ε*b*v₀ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right coupon bn) vn
    _ = _ := by dsimp [b,v₀];ring

end YM.Integration.WilsonMacroscopicUniformRemainder
