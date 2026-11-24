import YM.Integration.WilsonPublicForkBasis
import YM.Integration.WilsonThermometerWeakPairInventory

/-! The simultaneous original two-scale scalar hearing for arbitrary numerical
fields, charged by their inverse-normalized homogeneous coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkCharged
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log OPE.Prescription OPE.Orbits
open WilsonPublicForkRooms WilsonPublicForkGeometry WilsonPublicForkGeometry.Node WilsonThermometerWeakPairForms
open scoped Topology Classical BigOperators
variable {I:Type} [Fintype I]
local notation "sites" => WilsonPublicForkGeometry.position
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {P:Prescription F.sector.derivatives}
theorem original (bank:LogTrace F P)(hp:P.Coherent)(h:ℕ)(view:Viewers F)
    (d:↥(WilsonPublicForkGeometry.near I)→ℕ)(e:ℕ){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃(B:ℝ)(K:ℕ),0≤B ∧ ∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:E4),0<r → r≤t → (∀i,‖x i‖≤M) → ‖z‖≤M → 2*δ≤‖z‖ → (∀i j,i≠j→δ≤‖x i-x j‖) → r*M≤t*δ →
      ∀(v:Labels S d)(w:S.Field e),
        let X:=crop (sites r t x z) (WilsonPublicForkGeometry.near I)
        ‖WilsonThermometerWeakPairExpansion.residual (spectator F view) P h X 0 v (t • z) w‖≤
          (∏i:↥(WilsonPublicForkGeometry.near I),WilsonThermometerWeakPairInventory.rent P (d i) r (v i))*
            WilsonThermometerWeakPairInventory.rent P e t w*
            (B*(badge t*badge r)^K*(t+(r/t)^(h+1))):=by
  let A:=Lot F.sector.derivatives d
  let E:=↥(bands F.sector.derivatives e)
  choose b k positive0 wage using fun (a:A)(c:E)=>WilsonPublicForkBasis.original F bank hp h view a c mn dp
  let B:=∑a:A,∑c:E,b a c
  let K:=∑a:A,∑c:E,k a c
  refine ⟨B,K,Finset.sum_nonneg fun a _=>Finset.sum_nonneg fun c _=>positive0 a c,?_⟩
  have conf:∀ᶠt:ℝ in 𝓝[>]0,t≤1:=(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [conf,eventually_all.mpr fun a=>eventually_all.mpr (wage a)] with t top pay
  intro r x z rp rt hx hz fz xy gap v w
  have tp:=rp.trans_le rt
  have live:=WilsonPublicForkSeats.distinct rp rt dp hx fz xy gap
  have bb (u:ℝ)(up:0<u)(small:u≤1):1≤badge u:=by
    unfold badge OPE.run;linarith [Real.log_nonpos up.le small]
  have one:1≤badge t*badge r:=one_le_mul_of_one_le_of_one_le (bb t tp top) (bb r rp (rt.trans top))
  apply WilsonThermometerWeakPairInventory.original (spectator F view) P hp (spectate F view) F.room.kernel
    h _ 0 v _ w live.2.1 live.2.2.2 rp tp
  intro a c
  have money:b a c≤B:=(Finset.single_le_sum (f:=b a) (fun i _=>positive0 a i) (mem_univ c)).trans
    (Finset.single_le_sum (f:=fun i:A=>∑j:E,b i j) (fun i _=>Finset.sum_nonneg fun j _=>positive0 i j) (mem_univ a))
  have age:k a c≤K:=(Finset.single_le_sum (f:=k a) (fun _ _=>Nat.zero_le _) (mem_univ c)).trans
    (Finset.single_le_sum (f:=fun i:A=>∑j:E,k i j) (fun _ _=>Nat.zero_le _) (mem_univ a))
  refine (pay a c r x z rp rt hx hz fz xy gap).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact mul_le_mul money (pow_le_pow_right₀ one age) (pow_nonneg (zero_le_one.trans one) _)
    (le_trans (positive0 a c) money)
end YM.Integration.WilsonPublicForkCharged
end
