import YM.Integration.WilsonPublicForkTokens
import YM.Integration.WilsonThermometerWeakPairExpansion

/-! Each lodged running basis arm of the genuine three-point programme
carries only its own homogeneous grade and its own spatial length. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkBasis
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log OPE.Prescription OPE.Orbits
open WilsonPublicForkRooms WilsonPublicForkGeometry WilsonPublicForkGeometry.Node WilsonThermometerWeakPairForms
open scoped Topology Classical BigOperators
variable {I:Type} [Fintype I]
local notation "sites" => WilsonPublicForkGeometry.position
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {P:Prescription F.sector.derivatives}{d:↥(WilsonPublicForkGeometry.near I)→ℕ}{e:ℕ}
def lodged (a:Lot F.sector.derivatives d)(c:↥(bands F.sector.derivatives e))(j:Node I):C.book.Token:=
  if hj:j∈(WilsonPublicForkGeometry.near I) then P.letter (a (⟨j,hj⟩:↥(WilsonPublicForkGeometry.near I))).1 else P.letter c.1

private theorem cash (a:Lot F.sector.derivatives d)(c:↥(bands F.sector.derivatives e))(r t:ℝ):
    mass (lodged (I:=I) (d:=d) (e:=e) (P:=P) F a c) r t=(∏i:↥(WilsonPublicForkGeometry.near I),r^(a i).1.fst)*t^c.1.fst:=by
  let p:=lodged (I:=I) (d:=d) (e:=e) (P:=P) F a c
  have atHome (i:↥(WilsonPublicForkGeometry.near I)): P.letter (a i).1=p i.1:=by simp [p,lodged,i.2]
  have atFar: p far=P.letter c.1:=by simp [p,lodged,near]
  have equal:(∏i:↥(WilsonPublicForkGeometry.near I),r^(a i).1.fst)=∏i∈(WilsonPublicForkGeometry.near I),r^(p i).fst:=by
    refine Eq.trans ?_ (Finset.prod_attach (WilsonPublicForkGeometry.near I) (fun i=>r^(p i).fst))
    apply Finset.prod_congr rfl
    intro i _
    exact congr_arg (fun v:C.book.Token=>r^v.1) (atHome i)
  rw [equal]
  change r^(load p)*t^(p far).fst=_
  rw [atFar];simp [near,load,Finset.prod_pow_eq_pow_sum,Prescription.letter]

theorem original (bank:LogTrace F P)(hp:P.Coherent)(h:ℕ)(view:Viewers F)
    (a:Lot F.sector.derivatives d)(c:↥(bands F.sector.derivatives e)){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(b:ℝ)(K:ℕ),0≤b ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:E4),0<r → r≤t → (∀i,‖x i‖≤M) → ‖z‖≤M → 2*δ≤‖z‖ → (∀i j,i≠j→δ≤‖x i-x j‖) → r*M≤t*δ →
      let X:=crop (sites r t x z) (WilsonPublicForkGeometry.near I)
      (∏i:↥(WilsonPublicForkGeometry.near I),r^(a i).1.fst)*t^c.1.fst*
        ‖WilsonThermometerWeakPairExpansion.residual (spectator F view) P h X 0 (field P a)
          (t • z) (P.loaded c.1 e)‖≤ b*(badge t*badge r)^K*(t+(r/t)^(h+1)):=by
  let p:=lodged (I:=I) (d:=d) (e:=e) (P:=P) F a c
  obtain ⟨B,K,bp,wage⟩:=WilsonPublicForkTokens.original F bank p h view mn dp
  refine ⟨B,K,bp,?_⟩
  filter_upwards [wage] with t priced
  intro r x z rp rt hx hz fz xy gap
  let X:=crop (sites r t x z) (WilsonPublicForkGeometry.near I)
  let A:=spectator F view
  obtain ⟨_,left,_,right⟩:=WilsonPublicForkSeats.distinct rp rt dp hx fz xy gap
  have live:=priced r x z rp rt hx hz fz xy gap
  have nearReady (i:↥(WilsonPublicForkGeometry.near I)):WilsonThermometerWeakPairRise.Move F.sector.derivatives ((crop p (WilsonPublicForkGeometry.near I)) i) (names (field P a) i):=by
    have eq: (crop p (WilsonPublicForkGeometry.near I)) i=P.letter (a i).1:=by simp [crop,p,lodged,i.2]
    rw [eq];exact WilsonThermometerWeakPairRise.basis P (a i)
  have farReady (i:Unit):WilsonThermometerWeakPairRise.Move F.sector.derivatives (sole (p far) i)
      (names (sole (P.loaded c.1 e):Labels S (fun _:Unit=>e)) i):=by
    have eq:p far=P.letter c.1:=by simp [p,lodged,near]
    rw [eq];exact WilsonThermometerWeakPairRise.basis P c
  have shift:=WilsonThermometerWeakPairRise.discrepancy P hp F.room.kernel.laws.toSymmetric
    F.phase.transport.injection (spectate F view).laws.toSymmetric (spectate_respects F view) (spectate_ready F view)
    (x:=X) (y:=sole (t • z)) (o:=0) left right nearReady farReady h
  have filed:=discrepancy_old (T:=spectator F view) P h X 0 (field P a) (sole (t • z))
    (sole (P.loaded c.1 e):Labels S (fun _:Unit=>e)) (spectate F view) (spectate_respects F view) (spectate_ready F view) right
  rw [←cash (I:=I) (d:=d) (e:=e) (P:=P) F a c]
  exact (congrArg (fun u:ℂ=>mass p r t*‖u‖) (filed.trans shift.symm)).trans_le live
end YM.Integration.WilsonPublicForkBasis
end
