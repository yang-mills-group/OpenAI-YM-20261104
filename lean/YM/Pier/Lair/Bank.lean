import YM.Pier.Lair.Travel
import YM.Pier.Scene.Seed

/-! reuse EXACT level and M in RG17.Panoramic.ScenePlan. Transfer to any room.T frame on this F, including basis master costs.BOTH. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Lair
open Function Filter Set Table Extraction Climb Analysis Ward Spec
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank
open Next.UVStress Spin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f : Extraction.Order}{S:Table C.book}
variable (F: Final C f S) (h:G.Simple) {H : (Bel C.book).Hierarchy}
set_option quotPrecheck false
local notation "B" => (Bel C.book)
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "τ" => (turns C)
local notation "W₀" => (Maxwell.Free.scheme C.book.grid)
local notation "W₁" => F.sector.derivatives
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "H₁" => F.room.kernel
local notation "τ₁" => F.sector.turns
variable {X:Scaling S}{l: Ultrafilter (ℕ×ℕ)}{Z:Arch C}{V:∀ i, Vane C i}
open MeasureTheory SharpGram Lenses
open scoped ContDiff

variable {Y:ℝ→FamilyBasis (C:=C) S} (P:Present F Y) (d:ℕ)
open Weak.Portfolio OPE.Levy Push.FiniteDetection.Free
local notation "D₂"=> detectors
local notation "W₂"=>Pilot.trail
local notation "U!"=> (glass (Bel C.book) θ d)
local notation "K!"=> (glass S (H₁).spin d)
local instance (V:Gauge)(T:Register V)(L:Table T)(d:ℕ): FiniteDimensional ℝ (L.Field d) := Module.Finite.trans ℂ _

open RG17 Load RG12
variable {u : Filter (ℕ×ℕ)} (Q : Mantle F u) (E : OPE.Services C f S)
variable (L : Layout F)
include P E
local notation "β"=> C.path.levels.clock.hatBeta
local notation "𝔅" i=> β (L.level i)
-- MANY axes & limits. Payload priced with shift norm (not unshipped model only). identity natural under projection.and atRef equivalence preserved.Genuine over these coordinates.Basis allowances before mesh.Coupling near.Analogous Balance.
def tender (L:Layout F)(Y:ℝ→FamilyBasis (C:=C) S): Layout F:={ L with frame:=fun d r=> Y r d}
omit P E in
@[simp] lemma tickets (v:C.label d)(r:ℝ): master (tender F L Y) d r v= master L d r v:=rfl
structure Paying (Z:Layout F) (d:ℕ) : Prop where
    affordability : ∃ n:ℕ,∀ᶠ r in home, let c:=(C.path.levels.clock.hatBeta (Z.level r))^n
      (∀ v:Free C d,∃ w:C.label d,mass C d (Z.shift d r w) ≤ c*‖v‖ ∧ master Z d r w=Z.frame d r v) ∧
      ∀ v:C.label d, ‖(Z.frame d r).symm (master Z d r v)‖ ≤ c*mass C d (Z.shift d r v)
variable (hM:Pegs Q L)
    (hs:∀ᶠ r in Pilot.trail, C.S.a (L.level r)≤r ∧ r ≤ C.S.a (L.level r)*C.path.levels.clock.hatBeta (L.level r)^2)
include Q hM hs
lemma prices : Paying F (tender F L Y) d:=by
   obtain ⟨k,hk⟩:= across F P d Q E _ hM.level.growing hs
   have hV:= (Station.hat_rate C.path.levels E.simpleGate).comp hM.level.growing
   let p:=Lenses.price d
   refine ⟨k+p+1,?_⟩
   filter_upwards [engineeringPass Q L E hM d,hk,hV.eventually_ge_atTop 2,hV.eventually_ge_atTop (2*Lenses.bonus C d)] with r ⟨hr,hu⟩ hk hV hK
   let b:=β (L.level r); let a:= b^(k+p+1); let f:=Load.tent Q (L.level r) d
   have hp:2≤ b:=hV; have hx:0<b:=zero_lt_one.trans_le (le_trans one_le_two hp)
   change (∀ v,∃ w:C.label d,mass C d (L.shift d r w) ≤ a*_ ∧ master L d r w= Y r d v)∧∀ v, ‖(Y r d).symm (master L d r v)‖≤a*mass C d (L.shift d r v)
   constructor
   · intro v; let z:= f.symm (Y r d v)
     obtain ⟨w,hw,hZ⟩:= hr z
     refine ⟨(L.shift d r).symm w, ?_,?_⟩
     · rw [LinearEquiv.apply_symm_apply]
       have he:‖z‖ ≤ b^k*‖v‖:= by
           have hh:= hk.left (Y r d v); rw[LinearEquiv.symm_apply_apply] at hh; exact hh
       exact hw.trans ((mul_le_mul (mul_le_mul_of_nonneg_right hp (show 0 ≤ b^p from pow_nonneg hx.le _)) he (norm_nonneg z) (by positivity)).trans_eq (by unfold a; ring))
     unfold master; simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hZ]; rw[hM.frame]; exact LinearEquiv.apply_symm_apply ..
   intro v
   let w:=L.shift d r v; have hv: ‖f.symm (master L d r v)‖ ≤ 2 * Lenses.bonus C d * mass C d w:=by unfold f; rw [← hM.frame]; exact hu w
   refine (hk.right (master L d r v)).trans (le_trans (b:=b^k*(b*mass C d w)) ?_ ?_); apply mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_right hK (mass_nonneg ..))) (pow_nonneg hx.le _)
   rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..); rw [← pow_succ]; exact pow_le_pow_right₀ (one_le_two.trans hp) (by omega)

omit E P Q hM hs
namespace Paying
include E
open OPE OPE.Orbits OPE.Columns
variable (T: Paying F L d)
local notation "ρ"=> OPE.run
include T
lemma test (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)(v: RG17.Free C d) (ht: Reach C L.level)(j:Fin (d+1)) : RateLE home OPE.run (fun r=>R.cutTest j d (L.frame d r v)) (-(j.val:ℝ)):=by
   obtain ⟨k,hk⟩:=T.affordability; have he:= hk.mono fun r hr=> hr.1 v
   rw [eventually_iff_exists_mem] at he; obtain ⟨U,hU,h⟩:= he
   choose! w hW hw using h
   let z r:= L.shift d r (w r)
   have H:RateLE home ρ z 0:=by
       let A:=(crestArmour ht).power k
       have hr:= (A.pays ageLarge).mul (RateLE.const ‖v‖ ageLarge); rw [add_zero,mul_zero] at hr
       refine RateLE.of_norm_le hr (mem_of_superset hU (fun i hi=> (norm_le_mass ..).trans (hW i hi)))
   exact (engineeringUpper R L ht E d j.val z H).congr (mem_of_superset hU (fun i hi=> congrArg (R.cutTest j.val d) (hw i hi)))
end Paying
include E P Q hM hs
open OPE OPE.Orbits
lemma seated (hS:L.shift=(fun _ _=>LinearEquiv.refl ..))(R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) : Located (tender F L Y) ∧ Handles (tender F L Y) := by
   let U:= tender F L Y; have hh : U.shift=(fun _ _=> LinearEquiv.refl ..):=hS
   have ht: Reach C U.level:= hM.level
   let A:= Maxwell.Free.gear_laws C.labels
   refine ⟨byGrade R U ht (fun d=> by rw [hh]; exact RateLE.const _ ageLarge) ?_ (fun d=> ?_) (fun {i j} he=> P.grade F Y _ _ he) (fun d=> by rw [hh]; exact RateLE.const _ ageLarge) (fun d v j=> (prices F P d Q E L hM hs).test F d E (tender F L Y) R v ht j),?_⟩
   · rw[hh]; exact Eventually.of_forall fun _=>rfl
   · exact (P.scheme F Y d).mono fun r hi=> hi.unit
   refine ⟨(P.scheme F Y 4).mono fun r hi=>?_⟩
   exact ⟨Maxwell.Free.gear C.labels,Maxwell.Free.scheme C.labels,Maxwell.Free.hierarchy C.labels,(Load.single E.simpleGate).tensor,
     Maxwell.Free.gear_laws C.labels,Maxwell.Free.gear_motion C.labels, ⟨fun v x=>by change Y r 4 ((Bel C.book).mirror _ _ _ x)=_; rw[← A.signed,hi.axis]; exact F.phase.transport.spots.signed _ _ _, hi.real⟩, fun v x=> (hi.axis v x).symm,hi.unit⟩ -- change .frame r.v axis exact defeq
end YM.Pier.Lair
