import YM.Integration.WilsonGeneralArityBlockRoster
import YM.Integration.WilsonOriginalThreeCompactProduct

/-! The previously integrated connected words multiply on their common original vacuum at the next date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeneralArityBlockTable
open Function Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonRegisteredPairUnaryWallet WilsonGeneralArityBlockRoster
open scoped Classical BigOperators
variable {load:ℕ}
local notation "J" => Stock.census (Fin load)
local notation "W" => Stock.census Unit
variable {G:Gauge} {n:Side} {I:Type} [Fintype I] {O:I→Type} (owner:I→Fin load) (site:Fin load→Site n)
  (X:(i:I)→O i→Earn.Row (Passport.point (fun _:Unit=>site (owner i))) W G (Wallet disk))
local notation "M" => mounted owner site X

def value (f:I→ℂ) (v:Fin load) : ℂ := ∑i,if owner i=v then f i else 0

theorem grouped (f:I→ℂ) :
    (∑i:I,Poly.send ((J).fire (owner i)) (f i))=
      ∑v:Fin load,Poly.send ((J).fire v) (value owner f v) := by
  classical
  ext s
  simp only [Poly.part_sum,Poly.part_send,value]
  trans ∑i:I,∑v:Fin load,if s=(J).fire v then (if owner i=v then f i else 0) else 0
  · apply Finset.sum_congr rfl
    intro i _
    have swap (v:Fin load) :
        (if s=(J).fire v then (if owner i=v then f i else 0) else 0)=
        if owner i=v then (if s=(J).fire (owner i) then f i else 0) else 0 := by
      by_cases eq:owner i=v
      · simp [eq]
      · simp [eq]
    simp_rw [swap]
    simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h:s=(J).fire v <;> simp [h]


theorem original (y:ℝ)(x:Wallet (room load))(U:Config G n)(f:I→ℂ)
    (rows:∀i,HasSum (fun z=>(X i z).nominal y (project (owner i) x) U) (f i)):
    Spill.Foundry.uncut (M) y x U=∑i:I,Poly.send ((J).fire (owner i)) (f i) ∧
      Poly.pass (Spill.Foundry.uncut (M) y x U)=
        ∏v:Fin load,(1+Poly.send ((J).fire v) (value owner f v)):=by
  let a:(Σi:I,O i)→Poly J:=fun z=>Spill.raw (M) y x z U
  have csend (s:(J).Mode)(c:ℂ):c • Poly.send s 1=Poly.send s c:=by
    ext d
    simp only [Poly.part_smul,Poly.part_send]
    split_ifs <;> simp
  have raw (i:I)(z:O i):a ⟨i,z⟩=(X i z).nominal y (project (owner i) x) U • Poly.send ((J).fire (owner i)) 1:=
    (csend _ _).symm
  have row(i:I):HasSum (fun z:O i=>a ⟨i,z⟩) (Poly.send ((J).fire (owner i)) (f i)):=by
    simp only [raw]
    rw [←csend _ (f i)]
    exact (rows i).smul_const _
  have absSum(i:I):Summable (fun z:O i=>‖a ⟨i,z⟩‖):=by
    simp_rw [raw,norm_smul]
    exact (rows i).summable.norm.mul_right _
  have whole:Summable a:=((summable_sigma_of_nonneg (fun z=>norm_nonneg (a z))).2
    ⟨absSum,(hasSum_fintype _).summable⟩).of_norm
  have together:Spill.Foundry.uncut (M) y x U=∑i:I,Poly.send ((J).fire (owner i)) (f i):=by
    change (∑'z,a z)=_
    rw [whole.tsum_sigma]
    simp_rw [(row _).tsum_eq]
    exact tsum_fintype _
  refine ⟨together,?_⟩
  rw [together,grouped]
  exact Extra.Trajectories.pass_sum univ (J).fire (fun i _=>singleton_nonempty i) _

end YM.Integration.WilsonGeneralArityBlockTable
