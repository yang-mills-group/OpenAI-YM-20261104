import YM.Integration.WilsonThermometerCenteredScalar
import YM.Integration.WilsonMaxwellThermometerNominatedGroundLedger

/-! Seven-slot divided difference of the actual ordinary connected read.
The cofactor of each proper pair uses the independently filed singleton.
The coefficients of the singletons use the genuine physical proper pairs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedSecant
open Finset Marker WilsonPositionThermometerConnected WilsonThermometerCenteredAlgebra

open scoped Classical BigOperators
local notation "J₀"=>Stock.census (Fin 3)
local notation "Badge"=>Finset (Fin 3)

def faceKey : Fin 7→Badge := ![univ,{0,1},{0,2},{1,2},{0},{1},{2}]
def parcel (p q:Badge→ℂ):Fin 7→ℂ:=![1,-q {2},-q {1},-q {0},
  -p {1,2}+2*p {1}*p {2},-p {0,2}+2*q {0}*p {2},-p {0,1}+2*q {0}*q {1}]

def bill (p q:Badge→ℂ) (s:Badge):ℂ:=∑t:Fin 7,if s=faceKey t then parcel p q t else 0

private theorem transfer (p q h:Badge→ℂ):
    ∑s:Badge,bill p q s*h s=∑t:Fin 7,parcel p q t*h (faceKey t):=by
  simp only [bill,sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _=>?_
  simp [ite_mul]

/-- The exact two-correlation difference on the signed ordinary thermometer. -/
theorem signed (p q:Badge→ℂ):
    value p-value q=∑s:Badge,bill p q s*(p s-q s):=by
  rw [transfer]
  simp only [value,Fin.sum_univ_succ,Fin.sum_univ_zero,faceKey,parcel,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one,add_zero]
  ring

theorem filed (p q:Poly J₀) (hp:p.part (J₀).quiet=1) (hq:q.part (J₀).quiet=1):
    (Extra.Trajectories.connected p).part full-(Extra.Trajectories.connected q).part full=
      let P:=WilsonThermometerCenteredScalar.read p
      let Q:=WilsonThermometerCenteredScalar.read q
      ∑s:Badge,bill P Q s*(P s-Q s):=by
  have f:(Extra.Trajectories.connected p).part full=value (WilsonThermometerCenteredScalar.read p):=
    WilsonThermometerCenteredScalar.three p hp
  have g:(Extra.Trajectories.connected q).part full=value (WilsonThermometerCenteredScalar.read q):=
    WilsonThermometerCenteredScalar.three q hq
  rw [f,g]
  exact signed _ _

private theorem expense (p q:Badge→ℂ):
    ∑s:Badge,‖bill p q s‖≤∑t:Fin 7,‖parcel p q t‖:=by
  calc
    _≤∑s:Badge,∑t:Fin 7,‖(if s=faceKey t then parcel p q t else 0)‖:=
      sum_le_sum fun s _=>norm_sum_le _ _
    _=_:=by
      rw [sum_comm]
      refine sum_congr rfl fun t _=>?_
      simp [apply_ite norm]

/-- The enrolled numerical bill depends on the true six proper moments and
the three independent singleton values. No independent pair size enters it. -/
theorem budget (p q:Badge→ℂ) (a b:ℝ) (proper:∀s:Badge,s.Nonempty→s≠univ→‖p s‖≤a)
    (seed:∀i:Fin 3,‖q {i}‖≤b):
    let M:=max 1 (max a b)
    ∑s:Badge,‖bill p q s‖≤7*(M+2*M^2):=by
  let M:=max 1 (max a b)
  have one:1≤M:=le_max_left _ _
  have non:0≤M:=zero_le_one.trans one
  have pa:= (le_max_left a b).trans (le_max_right 1 (max a b))
  have qb:= (le_max_right a b).trans (le_max_right 1 (max a b))
  have f (i:Fin 3):‖p {i}‖≤M:=(proper _ (singleton_nonempty _) (by fin_cases i <;> decide)).trans pa
  have g (i:Fin 3):‖q {i}‖≤M:=(seed _).trans qb
  have h (i j:Fin 3):‖p {i,j}‖≤M:=(proper _ (insert_nonempty ..) (by fin_cases i <;> fin_cases j <;> decide)).trans pa
  have extra:M≤M+2*M^2:=by nlinarith [sq_nonneg M]
  have mixed {x y z:ℂ} (xx:‖x‖≤M) (yy:‖y‖≤M) (zz:‖z‖≤M):‖-x+2*y*z‖≤M+2*M^2:=by
    have pair:=mul_le_mul yy zz (norm_nonneg _) non
    calc
      _≤‖-x‖+‖2*y*z‖:=norm_add_le .. 
      _≤_:=by rw [norm_neg,norm_mul,norm_mul];norm_num; nlinarith
  have receipts (t:Fin 7):‖parcel p q t‖≤M+2*M^2:=by
    fin_cases t
    · simpa [parcel] using one.trans extra
    · simpa [parcel] using (g 2).trans extra
    · simpa [parcel] using (g 1).trans extra
    · simpa [parcel] using (g 0).trans extra
    · exact mixed (h 1 2) (f 1) (f 2)
    · exact mixed (h 0 2) (g 0) (f 2)
    · exact mixed (h 0 1) (g 0) (g 1)
  calc
    _≤_:=expense p q
    _≤∑_:Fin 7,(M+2*M^2):=sum_le_sum fun t _=>receipts t
    _=_:=by simp [nsmul_eq_mul,M,mul_add]

end YM.Integration.WilsonMaxwellThermometerNominatedSecant
