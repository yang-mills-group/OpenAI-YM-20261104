import YM.Integration.WilsonIndependentCollarFarCopies
import YM.Integration.WilsonIndependentCollarCensusAppointment

/-! Absolute far-copy return of the actual original issued lamps. Each
old relative lift takes its own addressed seat in the same appointment. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarIssuedCopies
open Function Finset Filter Lattice Wilson RG Precision QuadraticLocal Tree Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Wheel.Address FundedMarkedPathSelection OriginalIssuedMarkedRows
open WilsonOlderFreshConnectedRobe WilsonOlderFreshConnectedAppointment WilsonOlderFreshConnectedBirth
open scoped Classical BigOperators
variable {G:Gauge}{n e m:ℕ}{D k:Fin n→ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}

theorem original (R:Run G)(V:Realm G (e+1) Credit.leanC)(hm:V.anchor ≤ m)
    (app:Paid R V hm D k δ σ)(N:ℕ)(c:Fin n)(X:Input V hm S k D A)
    (included:J⊆S)(front:c∈J)(apos:0≤A)(top:m<N)(deep:0 < mass k J)
    (positive:0≤σ)(o:Cover)(v:Case D)(j:ℕ)(order:j≤e)(r:Fin (mass k J+j+1))
    (seats:Finset (Frill J c × RadP G r.val))(reach:ℕ)
    (far:∀u∈seats, reach≤feeH (toe J c o u.1) c J):
    let M:=R.family.path.levels.clock.hatBeta m^δ*A^J.card
    let T:=fun u=>WilsonOlderFreshConnectedBirth.issued R V hm app N c X included front apos top deep positive o v u
    ∑u∈seats,∑a:Stationary.Ink G r.val,
      (((T u.1).roll ⟨j,by omega⟩).leg ⟨⟨r,u,a⟩,rfl⟩).money (32*σ)
      ≤ (∏i∈J,‖v i‖)*(Real.exp (-(32*σ*reach))*M):=by
  intro M T
  let B:=∏i∈J,‖v i‖
  have b0:0≤B:=Finset.prod_nonneg fun i _=>norm_nonneg _
  let W:=fun u:Frill J c × RadP G r.val=>WilsonOlderFreshConnectedRoll.packet V hm X J c
    (mass k J) N o j r u
  have raw:Rooted V hm X J c (mass k J) N (32*σ) M o j r:=
    (app N S J c A X included front apos top).2 o j order r
  obtain ⟨μ,born,_word,tail⟩:=WilsonIndependentCollarFarCopies.original V hm X (by positivity) raw
  change ∑u∈seats,∑a:Stationary.Ink G r.val,(WilsonOlderFreshConnectedLamp.lamp (W u) v a).money (32*σ) ≤ _
  calc
    _≤∑u∈seats,B*lease (W u) (μ u) (32*σ):=Finset.sum_le_sum fun u _=>
      WilsonOlderFreshConnectedLamp.paid (W u) v (μ u) (born u) (32*σ)
    _=B*(∑u∈seats,lease (W u) (μ u) (32*σ)):=(Finset.mul_sum _ _ _).symm
    _≤_:=mul_le_mul_of_nonneg_left (tail seats reach far) b0

end YM.Integration.WilsonIndependentCollarIssuedCopies
end
