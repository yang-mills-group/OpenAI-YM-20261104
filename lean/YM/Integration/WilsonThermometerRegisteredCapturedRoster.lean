import YM.Integration.WilsonThermometerRegisteredCapturedWords
import YM.Integration.WilsonOlderFreshGraphMount

/-! Each partition of the enrolled finite mark set gives one paid scratch row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedRoster
open Lattice Wilson RG Marker Ac Gauge QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal.Poetry AllOrder AllOrder.Ink
open WilsonThermometerRegisteredCapturedWords
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V α ξ:Type*} [DecidableEq V] {P:Earn.Passport n V} {R:Census V}
local notation "Old" => Earn.Row P R G α
variable (w:V→Walk)

def degree (a:List Old):ℕ:=(a.map fun z=>z.lamp.e).sum
def angularRank (a:List Old):ℕ:=(a.map fun z=>z.lamp.r).sum
def allowed (a:List Old):ℕ:=(a.map fun z=>z.lamp.toll+1).sum
def extra (a:List Old):ℕ:=(a.map fun z=>z.lamp.r*(w z.binder.front).length).sum
def wages (a:List Old):ℝ:=(a.map fun z=>z.salary).prod
def weights (a:List Old) (t:α):ℂ:=(a.map fun z=>z.paint t).prod
def coefficient (a:List Old) (g:ℝ) (t:α) (U:Config G n):ℂ:=(a.map fun z=>z.nominal g t U).prod

private def one : Atom G 0 := ⟨Fin.elim0, fun _=>1⟩
private lemma one_value (x:Fin 0→G.Color) : (one (G:=G)).poly x=1 := by simp [one,Atom.poly]
private lemma one_law : (one (G:=G)).Invariant := by intro u x;rw [one_value,one_value]
private lemma one_budget (σ:ℝ) : (one (G:=G)).budget σ=1 := by
  simp [one,Atom.budget,Atom.length,Atom.magnitude]

def atom : (a:List Old)→Atom G (angularRank a)
  | [] => one
  | z::tail => joined (move (w z.binder.front) z.atom) (atom tail)

theorem law (a:List Old) : (atom w a).Invariant := by
  induction a with
  | nil=>exact one_law
  | cons z a h=>exact closed _ _ z.lawful h

theorem rank_le (a:List Old) : angularRank a≤degree a+allowed a := by
  induction a with
  | nil=>rfl
  | cons z a h=>
    change z.lamp.r+angularRank a≤z.lamp.e+degree a+(z.lamp.toll+1+allowed a)
    have bound:=z.lamp.crest
    omega

theorem size (a:List Old) (σ:ℝ) :
    (atom w a).budget σ=(a.map fun z=>z.atom.budget σ).prod*Real.exp (σ*(extra w a:ℝ)) := by
  induction a with
  | nil=>
    simp only [atom,List.map_nil,List.prod_nil,extra,List.sum_nil,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]
    exact one_budget _
  | cons z a h=>
    have movedCost : (move (w z.binder.front) z.atom).budget σ=
      z.atom.budget σ*Real.exp (σ*((z.lamp.r*(w z.binder.front).length:ℕ):ℝ)) := by
      unfold Atom.budget
      rw [WilsonThermometerRegisteredCapturedWords.reach,Nat.cast_add,mul_add,Real.exp_add]
      change z.atom.magnitude*(_*_)=_
      ring
    have combined (k l:ℕ) (A:Atom G k) (B:Atom G l):
        (joined A B).budget σ=A.budget σ*B.budget σ:=by
      unfold Atom.budget
      rw [WilsonThermometerRegisteredCapturedWords.size,WilsonThermometerRegisteredCapturedWords.length,Nat.cast_add,mul_add,Real.exp_add]
      ring
    change (joined _ (atom w a)).budget σ=_*Real.exp (σ*((z.lamp.r*(w z.binder.front).length+extra w a:ℕ):ℝ))
    rw [combined,movedCost,h,Nat.cast_add,mul_add,Real.exp_add]
    simp only [List.map_cons,List.prod_cons]
    ring

theorem products (a:List Old) (t:α) (g:ℝ) (hg:g≠0) (U:Config G n) (y:Site n)
    (incidence:∀v,stop y (w v)=P.origin v) :
    weights a t*(g^((degree a:ℤ)-(angularRank a:ℤ))*(atom w a).unmasked U y:ℝ)=coefficient a g t U := by
  induction a with
  | nil=>simp [weights,degree,angularRank,atom,coefficient,Atom.unmasked,one_value]
  | cons z a h=>
    have ex: ((degree (z::a):ℤ)-(angularRank (z::a):ℤ))=z.lamp.lag+((degree a:ℤ)-(angularRank a:ℤ)) := by
      change ((z.lamp.e+degree a:ℕ):ℤ)-((z.lamp.r+angularRank a:ℕ):ℤ)=_
      unfold Loan.lag
      push_cast
      ring
    change (z.paint t*weights a t)*(_*(joined (move (w z.binder.front) z.atom) (atom w a)).unmasked U y:ℝ)=
      z.nominal g t U*coefficient a g t U
    rw [ex,zpow_add₀ hg,group,moved _ _ z.lawful,incidence,←h]
    change _=z.paint t*(g^z.lamp.lag*z.atom.unmasked U (P.origin z.binder.front):ℝ)*_
    push_cast
    ring

variable {B:Earn.Passport n Unit} {D:Census Unit} (S:Earn.Binder B D)
variable (a:List Old) (d:ℕ) (hd:0<d) (limit:allowed a≤d+1)
    (σ:ℝ) (t:α) (χ:ℂ) (test:ξ→ℂ)

private def loan (a:List Old) (d:ℕ) (hd:0<d) (limit:allowed a≤d+1) : Loan where
  e:=degree a
  r:=angularRank a
  toll:=d
  higher:=hd
  crest:=calc
    angularRank a≤degree a+allowed a:=rank_le a
    _≤degree a+(d+1):=Nat.add_le_add_left limit _
    _=degree a+d+1:=(Nat.add_assoc ..).symm

private lemma positive_wage (a:List Old) : 0 < wages a := by
  induction a with
  | nil=>simp [wages]
  | cons z a h=>exact mul_pos z.sound h

private lemma tested_wage (a:List Old) (t:α) (paid:∀z∈a,z.Budget) : ‖weights a t‖≤wages a:=by
  induction a with
  | nil=>simp [weights,wages]
  | cons z a h=>
    change ‖z.paint t*weights a t‖≤z.salary*wages a
    rw [norm_mul]
    exact mul_le_mul (paid z (List.mem_cons_self ..) t)
      (h (fun z₀ hz₀=>paid z₀ (List.mem_cons_of_mem _ hz₀))) (norm_nonneg _) z.sound.le
def factor (w:V→Walk) (a:List Old) (σ:ℝ) : ℝ := Real.exp (σ*(extra w a:ℝ))
def row (w:V→Walk) (S:Earn.Binder B D) (a:List Old) (d:ℕ) (hd:0<d) (limit:allowed a≤d+1)
    (σ:ℝ) (t:α) (χ:ℂ) (test:ξ→ℂ) : Earn.Row B D G ξ where
  binder:=S
  lamp:=loan a d hd limit
  atom:=Bloom.letdown (atom w a) (factor w a σ)⁻¹
  lawful:=Bloom.claim _ _ (law w a)
  clear:=angularRank a=0
  salary:=factor w a σ*(max 1 ‖χ‖)*wages a
  sound:=by
    have e:0<factor w a σ:=Real.exp_pos _
    have pos:0 < max 1 ‖χ‖:=(show (0:ℝ)<1 by norm_num).trans_le (le_max_left _ _)
    exact mul_pos (mul_pos e pos) (positive_wage a)
  paint x:=(factor w a σ:ℂ)*χ*weights a t*test x
  rank:=id

private lemma budget_product (a:List Old) (σ:ℝ) (paid:∀z∈a,z.Graceful σ) :
    (a.map fun z=>z.atom.budget σ).prod≤1:=by
  induction a with
  | nil=>simp
  | cons z a h=>
    have nonneg:0≤z.atom.budget σ:=by unfold Atom.budget Atom.magnitude;positivity
    change z.atom.budget σ*(a.map fun z=>z.atom.budget σ).prod≤1
    exact (mul_le_mul_of_nonneg_left
      (h (fun z₀ hz₀=>paid z₀ (List.mem_cons_of_mem _ hz₀))) nonneg).trans
      (show z.atom.budget σ*1≤1 by simpa only [mul_one,Row.Graceful] using paid z (List.mem_cons_self ..))

theorem original (w:V→Walk) (S:Earn.Binder B D) (a:List Old) (d:ℕ) (hd:0<d) (limit:allowed a≤d+1)
    (σ:ℝ) (t:α) (χ:ℂ) (test:ξ→ℂ) (g:ℝ) (hg:g≠0) (U:Config G n) (x:ξ)
    (incidence:∀v,stop S.center (w v)=P.origin v)
    (legal:∀z∈a,z.Graceful σ ∧ z.Budget) (unit:∀v,‖test v‖≤1) :
    let T:=row w S a d hd limit σ t χ test
    T.nominal g x U=χ*test x*coefficient a g t U ∧ T.Graceful σ ∧ T.Budget ∧
      T.binder=S ∧ T.lamp.e=degree a ∧ T.lamp.r=angularRank a ∧ T.lamp.toll=d := by
  intro T
  have e:0<factor w a σ:=Real.exp_pos _
  have en:(factor w a σ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.ne'
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl⟩
  · change ((factor w a σ:ℂ)*χ*weights a t*test x)*
      (g^((degree a:ℤ)-(angularRank a:ℤ))*(Bloom.letdown (atom w a) (factor w a σ)⁻¹).unmasked U S.center:ℝ)=_
    rw [Bloom.grant,←products w a t g hg U S.center incidence]
    push_cast
    field_simp [en]
  · change (Bloom.letdown (atom w a) (factor w a σ)⁻¹).budget σ≤1
    rw [Bloom.reduce_charge,abs_of_pos (inv_pos.mpr e),size]
    have small:(a.map fun z=>z.atom.budget σ).prod≤1:=budget_product a σ (fun z hz=>(legal z hz).1)
    change (factor w a σ)⁻¹*(_*factor w a σ)≤1
    rwa [mul_left_comm,inv_mul_cancel₀ e.ne',mul_one]
  · intro v
    have paint:=tested_wage a t (fun z hz=>(legal z hz).2)
    change ‖(factor w a σ:ℂ)*χ*weights a t*test v‖≤factor w a σ*max 1 ‖χ‖*wages a
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos e]
    apply (mul_le_of_le_one_right (by positivity) (unit v)).trans
    gcongr
    exact le_max_right _ _

end YM.Integration.WilsonThermometerRegisteredCapturedRoster
