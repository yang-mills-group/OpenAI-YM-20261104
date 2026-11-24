import YM.Integration.WilsonOriginalMixedBlockRows
import YM.Integration.WilsonGeneralArityBlockTable

/-! The square-free ordinary table of the complete independent mixed log on every real
link field, with one input leg for each of its original enrolled source names. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedBlockTable
open Function Finset Lattice Laurent RG Wilson Marker Multi Gauge
open Push Push.AbsoluteSums Push.Local Paths Animals ConnectedActivityE6 QuadraticLocal
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonRegisteredPairUnaryWallet WilsonOriginalMixedBlockRows
open scoped Classical BigOperators

variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] {O:I→Type}
  {G:Gauge} {n:Side} {P:Passport n V} (B:I→Earn.Binder P (Stock.census V))
  (X:(i:I)→O i→Earn.Row (Passport.point (fun _:Unit=>(B i).center)) (Stock.census Unit) G (Wallet disk))

local notation "M"=>mounted B X
local notation "J"=>Stock.census V
theorem original (y:ℝ)(x:Wallet (room V))(U:Config G n)(f:I→ℂ)
    (rows:∀i,HasSum (fun z=>(X i z).nominal y (project (B i).mode x) U) (f i)):
    Spill.Foundry.uncut (M) y x U=∑i:I,Poly.send (B i).mode (f i) ∧
      Poly.pass (Spill.Foundry.uncut (M) y x U)=
        ∏i:I,(1+Poly.send (B i).mode (f i)):=by
  let a:(Σi:I,O i)→Poly J:=fun z=>Spill.raw (M) y x z U
  have csend (s:(J).Mode)(c:ℂ):c • Poly.send s 1=Poly.send s c:=by
    ext d
    simp only [Poly.part_smul,Poly.part_send]
    split_ifs <;> simp
  have raw (i:I)(z:O i):a ⟨i,z⟩=(X i z).nominal y (project (B i).mode x) U • Poly.send (B i).mode 1:=
    (csend _ _).symm
  have row(i:I):HasSum (fun z:O i=>a ⟨i,z⟩) (Poly.send (B i).mode (f i)):=by
    simp only [raw]
    rw [←csend _ (f i)]
    exact (rows i).smul_const _
  have absSum(i:I):Summable (fun z:O i=>‖a ⟨i,z⟩‖):=by
    simp_rw [raw,norm_smul]
    exact (rows i).summable.norm.mul_right _
  have whole:Summable a:=((summable_sigma_of_nonneg (fun z=>norm_nonneg (a z))).2
    ⟨absSum,(hasSum_fintype _).summable⟩).of_norm
  have together:Spill.Foundry.uncut (M) y x U=∑i:I,Poly.send (B i).mode (f i):=by
    change (∑'z,a z)=_
    rw [whole.tsum_sigma]
    simp_rw [(row _).tsum_eq]
    exact tsum_fintype _
  refine ⟨together,?_⟩
  rw [together]
  exact Extra.Trajectories.pass_sum univ (fun i=>(B i).mode) (fun i _=>⟨(B i).front,(B i).east⟩) f


end YM.Integration.WilsonOriginalMixedBlockTable
end
