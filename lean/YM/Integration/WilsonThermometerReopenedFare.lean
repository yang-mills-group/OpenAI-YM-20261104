import YM.Integration.WilsonThermometerUnchangedGrouping
import YM.RG05Readout.Capture.Invoices

/-! The authentic paid positive hard and site budget buys the expense of retaining each singleton at its own displaced reporter between two joins. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerReopenedFare
open Function Filter Finset MeasureTheory Relation Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Ribbon Menu Marker Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Ribbons Ribbons.Fibers Ribbons.ManyCopies
open Ribbons.ManyCopies.Muster RG05Readout RG05Readout.Address RG05Readout.Many
open MergeProof.Ribbons PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage PhysicalNext.Repeat.Mallow
open scoped Topology Classical BigOperators

private theorem strip {B M:ℕ} {α η t:ℝ} (marks:1≤M) (heat:0<η) (cash:0≤t)
    (funded:((B+B+1:ℕ):ℝ)^4*Ribbons.Salt.scent B M α 1 η 1 t≤1/2):
    η*Real.exp α≤1:=by
  have hM:1≤(M:ℝ):=by exact_mod_cast marks
  have line:0 ≤ Ribbons.Salt.scent B M α 1 η 1 t:=by unfold Ribbons.Salt.scent;positivity
  have volume:1 ≤ ((B+B+1:ℕ):ℝ)^4:=one_le_pow₀ (by exact_mod_cast (show 1≤B+B+1 by omega))
  have small: Ribbons.Salt.scent B M α 1 η 1 t≤1/2 := (le_mul_of_one_le_left line volume).trans funded
  let X:ℝ:=(M:ℝ)*1*Real.exp α+1
  have hx:Real.exp α≤X:= by
    unfold X;rw [mul_one];exact le_add_of_le_of_nonneg (le_mul_of_one_le_left (Real.exp_pos α).le hM) zero_le_one
  have hx':0≤η*X:=mul_nonneg heat.le ((Real.exp_pos _).le.trans hx)
  have leading:η*Real.exp α≤(1+(M:ℝ))*η*X:=by
    rw [mul_assoc];exact (mul_le_mul_of_nonneg_left hx heat.le).trans (le_mul_of_one_le_left hx' (le_add_of_nonneg_right (Nat.cast_nonneg M)))
  have extra:0≤(1+(M:ℝ))*t:=by positivity
  change (1+(M:ℝ))*η*X+(1+(M:ℝ))*η*X+(1+(M:ℝ))*t ≤1/2 at small
  linarith

theorem price {x α w:ℝ} (hot:0<x) (width:0<w)
    (already:probe x*Real.exp α≤1) :
    (probe x*w/Real.exp α)⁻¹ ≤ x^4*w⁻¹:= by
  have aperture : probe x=(x^2)⁻¹:=by unfold probe;rw [Real.rpow_neg hot.le];norm_num
  have he:Real.exp α≤x^2:=by
    rw [aperture,inv_mul_le_iff₀ (by positivity),mul_one] at already
    exact already
  calc
    (probe x*w/Real.exp α)⁻¹ = (x^2*Real.exp α)*w⁻¹:=by rw [aperture];field_simp
    _ ≤ (x^2*x^2)*w⁻¹:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (inv_nonneg.mpr width.le)
    _ = _:=by ring

variable {G:Gauge} (A:History G) {N m p:ℕ} {I:Type} [Fintype I] [DecidableEq I]
local notation "P" => A.rep N p m
local notation "Y" => Stock.census (Unit×I)
local notation "M" => apron A.levels m
local notation "η" => renal A.levels m
local notation "α" => (P).p.supportExponent
local notation "β" => A.levels.clock.hatBeta (m+1)

theorem original {d:GaugeDoor (A.rep N p (m+1)) (P)} {a t:ℝ}
    (course:Coursework A (apron A.levels) d (η) a t) (funded:(P).p=A.levels.budget m)
    (bill:let s:=Ribbons.scurry A.levels (apron A.levels) (fun _=>t) (η) m
      (((A.levels.budget m).B+(A.levels.budget m).B+1:ℕ):ℝ)^4*s≤1/2 ∧ Real.exp s-1≤1)
    {rows:Unit×I→Three G (A.S.side m p)} {X:Config G (A.S.side m p)→Poly (Y)}
    {o:Unit×I→Site (A.S.side m p)} {w:Unit×I→ℝ} {z y:ℝ}
    (cap:Alcove (P) rows X o w t (η) (1/2)) (stock:Arsenal (P)) (valid:(P).activities.Valid (P).p z y)
    (nz:∀ U,(P).eval U≠0) (live:Integrable X (prior G _)) (homes:Occupancy o (M)) (width:∀i,0<w i):
    MenuBoard (P) rows X o (fun i=> (η)*w i/Real.exp ((α)+1/2)) ((α)-2) 1 ∧
      ∀i,((η)*w i/Real.exp ((α)+1/2))⁻¹≤(β)^4*(w i)⁻¹:=by
  have pos:0≤t:=by
    obtain ⟨_,_,_,_,_,raw,-⟩:=cap.chamber
    obtain ⟨s,_,hit,-⟩:=raw
    exact (tsum_nonneg ((hit 0).1)).trans (hit 0).2.2
  have mass:0<(M):=by unfold apron;exact Nat.mul_pos (by omega) (pow_pos (A.S.block m).property _)
  have tariff:(2:ℝ)≤(α):=by rw [funded];exact (show (2:ℝ)≤100 by norm_num).trans course.poses.exp.1
  have volumes:(((P).p.B+(P).p.B+1:ℕ):ℝ)^4*(t+(M)*siteFactor (P).p.B*(η))≤1/2:=by
    rw [funded];exact course.poses.stakes.1
  have meals:(((P).p.B+(P).p.B+1:ℕ):ℝ)^4*Ribbons.Salt.scent (P).p.B (M) ((α)+1/2) 1 (η) 1 t≤1/2 ∧
      Real.exp (Ribbons.Salt.scent (P).p.B (M) ((α)+1/2) 1 (η) 1 t)-1≤1:=by
    rw [funded];exact bill
  have full:=WilsonThermometerUnchangedGrouping.original (P) rows X o w cap stock valid nz live homes width tariff pos
    course.poses.hats.1 course.poses.hats.2 volumes meals
  refine ⟨full,fun i=>price (zero_lt_one.trans (A.levels.fits.delayed _)) (width i) ?_⟩
  exact strip mass course.poses.hats.1 pos meals.1

end YM.Integration.WilsonThermometerReopenedFare
end
