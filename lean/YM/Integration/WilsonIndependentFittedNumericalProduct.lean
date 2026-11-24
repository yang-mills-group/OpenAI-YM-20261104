import YM.Integration.WilsonPhysicalMarkedDefectRawCartesian
import YM.Integration.WilsonOriginalPublicPlantedPivotFields

/-! A single truncation of a fitted normalized moment on its actual finite tree. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentFittedNumericalProduct
open Finset PowerSeries XSpace XSpace.Cirrus
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped Classical BigOperators

private theorem flip (Q:ℕ)(u:ℝ)(A:PowerSeries ℂ):
    cash Q (-u) (PowerSeries.rescale (-1:ℂ) A)=cash Q u A:=by
  unfold cash
  refine sum_congr rfl (fun e _=>?_ )
  rw [Complex.ofReal_neg,coeff_rescale,←mul_assoc,←mul_pow]
  simp

private theorem same_belt (Q:ℕ)(A:PowerSeries ℂ):
    belt Q (PowerSeries.rescale (-1:ℂ) A)=belt Q A:=by
  simp [belt,coeff_rescale,norm_pow]

theorem signed {I:Type}(Q:ℕ){u:ℝ}(small:|u|≤1)(s:Finset I)(f:I→PowerSeries ℂ):
    ‖(∏i∈s,cash Q u (f i))-cash Q u (∏i∈s,f i)‖≤
      s.card*|u|^(Q+1)*(∏i∈s,belt Q (f i)):=by
  by_cases pos:0≤u
  · rw [abs_of_nonneg pos] at small ⊢
    exact WilsonPhysicalMarkedDefect.RawProduct.whole Q pos small s f
  · have neg:u<0:=lt_of_not_ge pos
    rw [abs_of_neg neg] at small ⊢
    have paid:=WilsonPhysicalMarkedDefect.RawProduct.whole Q (neg_pos.mpr neg).le small s
      (fun i=>PowerSeries.rescale (-1:ℂ) (f i))
    rw [←map_prod] at paid
    simpa only [flip,same_belt] using paid

theorem added {I:Type}(Q:ℕ)(u:ℝ)(s:Finset I)(f:I→PowerSeries ℂ):
    cash Q u (∑i∈s,f i)=∑i∈s,cash Q u (f i):=by
  unfold cash
  simp_rw [map_sum,Finset.mul_sum]
  exact sum_comm

variable {G:Gauge}(W:Initialize G){n:ℕ}(x:Sample n)
variable {I:Type}[Fintype I]{α:I→Type}[∀i,Fintype (α i)]
local notation "T" => W.tree x.F.p
variable (P:(i:I)→α i→Bare.Series (W.tree x.F.p) G)(D:(i:I)→α i→PowerSeries ℂ)

def pivot (a:(i:I)→α i):PowerSeries ℂ:=Bare.normalized T G (∏i,P i (a i))

def fitted : PowerSeries ℂ:=
  Bare.normalized T G (∏i,∑a,Bare.scalar T (D i a)*P i a)

theorem expanded:
    fitted W x P D=∑a:(i:I)→α i,(pivot W x P a)*(∏i,D i (a i)):=by
  simp only [fitted,Fintype.prod_sum,map_sum]
  refine sum_congr rfl (fun a _=>?_ )
  rw [prod_mul_distrib,show
      (∏i,Bare.scalar (G:=G) T (D i (a i)))=Bare.scalar T (∏i,D i (a i)) from
      (map_prod (PowerSeries.map (algebraMap ℂ (Bare.Vertices T G))) _ univ).symm,
      Bare.normalized_scalar]
  exact mul_comm _ _

def numerical (Q J:ℕ)(u:ℝ):ℂ:=
  ∑a:(i:I)→α i,(∏i,cash Q u (D i (a i)))*cash J u (pivot W x P a)

def gross (Q:ℕ):ℝ:=
  ∑a:(i:I)→α i,belt Q (pivot W x P a)*(∏i,belt Q (D i (a i)))

def wage (Q:ℕ)(u:ℝ):ℝ:=
  ∏i,∑a,‖cash Q u (D i a)‖

theorem regroup (Q:ℕ){u:ℝ}(small:|u|≤1):
    ‖cash Q u (fitted W x P D)-numerical W x P D Q Q u‖≤
      ((Fintype.card I:ℝ)+1)*|u|^(Q+1)*gross W x P D Q:=by
  rw [expanded,added]
  unfold numerical gross
  rw [←sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a _
  let f:Option I→PowerSeries ℂ:=fun i=>i.elim (pivot W x P a) (fun j=>D j (a j))
  have paid:=signed Q small univ f
  simp only [Fintype.prod_option,f,Option.elim_none,Option.elim_some,card_univ,
    Fintype.card_option,Nat.cast_add,Nat.cast_one] at paid
  rw [norm_sub_rev,mul_comm (∏i,cash Q u (D i (a i)))]
  exact paid

theorem retained (Q J:ℕ){u ε:ℝ}(small:|u|≤1)
    (tail:∀a,‖cash Q u (pivot W x P a)-cash J u (pivot W x P a)‖≤ε):
    ‖cash Q u (fitted W x P D)-numerical W x P D Q J u‖≤
      ((Fintype.card I:ℝ)+1)*|u|^(Q+1)*gross W x P D Q+wage D Q u*ε:=by
  have loss:‖numerical W x P D Q Q u-numerical W x P D Q J u‖≤wage D Q u*ε:=by
    unfold numerical wage
    rw [←sum_sub_distrib,Fintype.prod_sum,sum_mul]
    apply (norm_sum_le _ _).trans
    refine sum_le_sum (fun a _=>?_ )
    rw [←mul_sub,norm_mul,norm_prod]
    exact mul_le_mul_of_nonneg_left (tail a) (prod_nonneg fun i _=>norm_nonneg _)
  exact (calc
    _≤‖cash Q u (fitted W x P D)-numerical W x P D Q Q u‖+
        ‖numerical W x P D Q Q u-numerical W x P D Q J u‖:=by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (cash Q u (fitted W x P D)-numerical W x P D Q Q u)
        (numerical W x P D Q Q u-numerical W x P D Q J u)
    _≤_:=add_le_add (regroup W x P D Q small) loss)

end YM.Integration.WilsonIndependentFittedNumericalProduct
