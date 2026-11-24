import YM.Integration.WilsonIndependentNotebookRawInvoice
import YM.Integration.WilsonIndependentNotebookReflectedPoint

/-! The literal Wilson group field includes its own angular-rank thermal charge. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookRawSeat
open Function Filter Finset Lattice RG Wilson Source Labels XSpace XSpace.Rose XSpace.Cirrus
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain PowerSeries
open WilsonIndependentNotebookConstantSeat (seat part issue constant)
open WilsonIndependentMatchedFiledIncome (plate allot charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonAddressedTrialPivotUnits (row)
open WilsonIndependentConditionedBankRawUnits (home)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalPhysicalFruitVerse (written)
open scoped BigOperators Classical
variable {G:Gauge}{d D:ℕ}{F:Labels.Frame G d}

def component (im:Bool):ℂ →L[ℝ] ℝ:=if im then Complex.imCLM else Complex.reCLM

theorem ground (a:Alma F):rankS (notar F a)=0 ↔ a=seat F (sheet F a):=by
  constructor
  · intro no
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · rfl
    · apply Subtype.ext
      exact Multiset.card_eq_zero.mp no
  · intro eq
    conv_lhs => rw [eq]
    simp [seat,notar,rankS]

theorem allowance (e n:ℕ)(s A:ℝ)(non:0≤A):
    allot e (monomial n s) A≤allot e (C s) A:=by
  rw [constant]
  have one (j:ℕ):(∑t∈Finset.HasAntidiagonal.antidiagonal j,|coeff t.1 (monomial n s)| * A) ≤ |s| * A:=by
    by_cases old:n ≤ j
    · rw [sum_eq_single (n,j-n)]
      · simp
      · intro t ht ne
        have note:=Finset.HasAntidiagonal.mem_antidiagonal.mp ht
        have neq:t.1≠n:=fun eq=>ne (Prod.ext eq (by omega))
        simp [coeff_monomial,neq]
      · simp [Nat.add_sub_of_le old]
    · rw [sum_eq_zero (fun t ht=>?_)];exact mul_nonneg (abs_nonneg _) non
      have note:=Finset.HasAntidiagonal.mem_antidiagonal.mp ht
      have ne:t.1≠n:=by omega
      simp [coeff_monomial,ne]
  exact (sum_le_sum fun j _=>one j).trans_eq (by simp [nsmul_eq_mul])

theorem charged (w:F.Coeff)(im:Bool)(e:ℕ)(A:Alma F→ℝ)(non:∀i,0≤A i):
    charge e (written F w (component im)) A≤charge e (issue F im w) A:=by
  apply sum_le_sum
  intro a _
  by_cases yes:rankS (notar F a)=0
  · have eq:= (ground a).mp yes
    change allot _ (if rankS (notar F a)=0 then _ else _) _ ≤ _
    rw [if_pos yes,issue,if_pos eq]
    have term:component im (w (sheet F a))=part im (w (sheet F a)):=by cases im <;> rfl
    rw [term]
    exact allowance _ _ _ _ (non a)
  · have ne:=mt (ground a).mpr yes
    change allot _ (if rankS (notar F a)=0 then _ else _) _ ≤ _
    rw [if_neg yes,issue,if_neg ne]

theorem field (w:F.Coeff)(p:ℂ →L[ℝ] ℝ)(τ:ℝ):written F (τ • w) p=τ • written F w p:=by
  funext a
  ext1 n
  by_cases g:rankS a.val.2=0
  · have term:p ((τ:ℂ)*w (sheet F a))=τ*p (w (sheet F a)):=by
      simpa only [Complex.real_smul,smul_eq_mul] using p.map_smul τ (w (sheet F a))
    simp [written,g,coeff_monomial,Pi.smul_apply,term]
  · simp [written,g]

theorem wages (e:ℕ)(A:Alma F→ℝ)(v:Verse F){τ:ℝ}(pos:0≤τ):
    charge e (τ • v) A=τ*charge e v A:=by
  unfold charge allot
  simp only [Pi.smul_apply,map_smul,smul_eq_mul,abs_mul,abs_of_nonneg pos,mul_assoc,Finset.mul_sum]

theorem original (R:Run G)(W:Initialize G)(survey:Bool)(fit:d<D)(e:ℕ)
    (A:Alma (R.family.labels.level d)→ℝ)(non:∀i,0≤A i)
    {j f K N p target:ℕ}(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
    (S:(R.family.label d)≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){salary:ℝ}
    (paid:Cash (R:=R) d j f K N p target before up live η S Y salary)
    (arm:Arm R d N p f K)(same:arm.w=S.symm (fitted R d j N p Y))(t:ℂ)(im:Bool):
    let F:=R.family.labels.level d
    let δ:=R.family.S.a K/R.family.S.a f
    let z:=row R d K N p t (coords R arm)
    let M:=∑i:F.Index,A (seat F i)
    let c:=written F ((δ^d) • z) (component im)
    let T:=sectionAt R W survey d
    Shrine (plate T fit) c=(δ^d) • Shrine (plate T fit) (written F z (component im)) ∧
      charge e c A=δ^d*charge e (written F z (component im)) A ∧
      charge e c A≤(e+1:ℕ)*M*(home R d j f η t salary*δ^(-η)):=by
  intro F δ z M c T
  have pn:0≤δ^d:=pow_nonneg (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos f).le) _
  have real:=WilsonIndependentNotebookRawInvoice.original R W survey fit e A non before up live S Y paid arm same t im
  have shape:c=(δ^d) • written F z (component im):=field z (component im) _
  refine ⟨?_,?_,(charged ((δ^d) • z) im e A non).trans real.2.2⟩
  · rw [shape,WilsonCoeffUV.StableStrip.shrine_μ]
  · rw [shape,wages _ _ _ pn]
end YM.Integration.WilsonIndependentNotebookRawSeat
