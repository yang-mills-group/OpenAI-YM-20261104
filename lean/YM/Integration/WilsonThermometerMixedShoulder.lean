import YM.Integration.WilsonThermometerMixedGallery
import YM.Integration.WilsonOriginalPrecontactRestoration
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedShoulder
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push Push.Corrected Push.AbsoluteSums
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe QuadraticLocal.Fusion QuadraticLocal.Fusion.Attached
open WilsonThermometerMixedGallery
open scoped Classical BigOperators
variable {R:Marker.Census (Fin 3)} {G:Gauge} {n:Side} {P:Rep G n} {o:Fin 3→Site n}
  {X ι:Type} {p:BudgetPoint} {F:ℕ→ForcedAddress G n} {K:Code G n}
  {w:Fin 3→ℝ} {a e b M k:ℝ} {B:ℕ}

def picked (old:Lamps X ι G p o R)(reg:ι→R.Mode→Prop):Set ι:=
  {i|1<(old.mode i).val.card ∧ reg i (old.mode i)}

private theorem extendBill (S:Set ι)(f:S→ℝ){C:ℝ}(paid:SumBudget f C):
    SumBudget (fun i=>if h:i∈S then f ⟨i,h⟩ else 0) C:=by
  let inc:S→ι:=fun i=>i.val
  have inj:Injective inc:=Subtype.val_injective
  have spread:HasSum (Function.extend inc f 0) (∑'i,f i):=(hasSum_extend_zero inj).2 paid.2.1.hasSum
  have eq:(fun i=>if h:i∈S then f ⟨i,h⟩ else 0)=Function.extend inc f 0:=by
    funext i
    by_cases h:i∈S
    · simpa only [dif_pos h] using (inj.extend_apply f 0 ⟨i,h⟩).symm
    · have outside:i∉Set.range inc:=by rintro ⟨j,rfl⟩;exact h j.property
      rw [dif_neg h];exact (Function.extend_apply' f (0:ι→ℝ) i outside).symm
  refine ⟨fun i=>?_,?_,?_⟩
  · dsimp only;split
    next h=>exact paid.1 ⟨i,h⟩
    next=>exact le_rfl
  · rw [eq];exact spread.summable
  · rw [eq,spread.tsum_eq];exact paid.2.2

/-- Only already mixed incoming regular occurrences pay the amplification. The charge is
rooted on their original support, with the very same derivative order and healthy predicate. -/
theorem regular (old:Lamps X ι G p o R)(reg:ι→R.Mode→Prop)(c:ℂ)(hw:∀v,0<w v)
    (all:old.Paid w B a e)
    (mixed:(WilsonPrecontactSeparatedLamps.portion old (picked old reg)).Paid w B a M):
    (lamps c reg old).Paid w B a (e+‖c‖*M):=by
  classical
  let S:=picked old reg
  obtain ⟨f,fn,fs,bill⟩:=all.budget
  obtain ⟨g,gn,gs,small⟩:=mixed.budget
  let F:ι→ℝ:=fun i=>if h:i∈S then ‖c‖*g ⟨i,h⟩ else f i
  refine ⟨F,fun i=>?_,fun i x v hv=>?_,fun v=>?_⟩
  · dsimp only [F];split
    next h=>exact mul_nonneg (norm_nonneg _) (gn ⟨i,h⟩)
    next=>exact fn i
  · by_cases selected:i∈S
    · change p.supBounds v (old.ground i) (rent c (reg i) (old.mode i) • old.nominal x i) (F i)
      rw [show rent c (reg i) (old.mode i)=c from if_pos selected,show F i=‖c‖*g ⟨i,selected⟩ from dif_pos selected]
      exact Next.Foundations.bound_smul c (gs ⟨i,selected⟩ x v hv)
    · change p.supBounds v (old.ground i) (rent c (reg i) (old.mode i) • old.nominal x i) (F i)
      rw [show rent c (reg i) (old.mode i)=1 from if_neg selected,show F i=f i from dif_neg selected,one_smul]
      exact fs i x v hv
  · let rate:ι→ℝ:=fun i=>if v∈old.ground i then Poly.toll w (old.mode i)*F i*Real.exp (a*coverNumber B (old.ground i)) else 0
    let low:S→ℝ:=fun j=>if v∈old.ground j.val then Poly.toll w (old.mode j.val)*g j*Real.exp (a*coverNumber B (old.ground j.val)) else 0
    have high:=budget_plus (bill v) (budget_scale (norm_nonneg c) (extendBill S low (small v)))
    change SumBudget rate _
    apply budget_mono high
    · intro i
      by_cases mem:v∈old.ground i
      · dsimp only [rate];rw [if_pos mem]
        apply mul_nonneg (mul_nonneg (Poly.worth hw _).le _) (Real.exp_pos _).le
        dsimp only [F];split
        next h=>exact mul_nonneg (norm_nonneg _) (gn ⟨i,h⟩)
        next=>exact fn i
      · simp [rate,mem]
    · intro i
      change rate i≤(if v∈old.ground i then Poly.toll w (old.mode i)*f i*Real.exp (a*coverNumber B (old.ground i)) else 0)+
        ‖c‖*(if h:i∈S then low ⟨i,h⟩ else 0)
      by_cases selected:i∈S
      · by_cases mem:v∈old.ground i
        · simp only [rate,F,low,if_pos mem,dif_pos selected]
          have base:=mul_nonneg (mul_nonneg (Poly.worth hw (old.mode i)).le (fn i)) (Real.exp_pos (a*coverNumber B (old.ground i))).le
          linarith only [base,show Poly.toll w (old.mode i)*(‖c‖*g ⟨i,selected⟩)*Real.exp (a*coverNumber B (old.ground i))=
            ‖c‖*(Poly.toll w (old.mode i)*g ⟨i,selected⟩*Real.exp (a*coverNumber B (old.ground i))) by ring]
        · simp [rate,low,mem,selected]
      · simp [rate,F,selected]

/-- Retain the entire hard cover and its original once-divided price. -/
theorem forced (old:Hard X p F K o R)(use:ℕ→R.Mode→Prop)(c:ℂ)
    (all:old.Paid w B a k): (hard c use old).Paid w B a (max 1 ‖c‖*k):=by
  let m:=max 1 ‖c‖
  have mpos:0 ≤ m :=(zero_le_one).trans (le_max_left _ _)
  obtain ⟨f,allows,bill⟩:=all.wages
  refine ⟨fun i=>(m:ℂ) • f i,?_,?_⟩
  · intro i x U s
    have h:=allows i x U s
    change ‖rent c (use i) s*(old.hard x i U).part s‖≤(((m:ℂ)*(f i).part s).re) ∧ (((m:ℂ)*(f i).part s).im)=0
    have bound:‖rent c (use i) s‖ ≤ m :=by
      unfold rent;split
      next=>exact le_max_right _ _
      next=>rw [norm_one];exact le_max_left (1:ℝ) ‖c‖
    rw [norm_mul,Complex.re_ofReal_mul,Complex.im_ofReal_mul]
    exact ⟨mul_le_mul bound h.1 (norm_nonneg _) mpos,by rw [h.2,mul_zero]⟩
  · intro v
    have h:=budget_scale mpos (bill v)
    convert h using 1
    funext i
    by_cases mem:v∈(F i).support
    · simp only [if_pos mem,Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg mpos,mul_assoc]
    · simp only [if_neg mem,mul_zero]

theorem paid (A:Gallery X ι o P R)(reg:ι→R.Mode→Prop)(use:ℕ→R.Mode→Prop)(c:ℂ)(hw:∀v,0<w v)
    (all:A.Pays w a e k)
    (small:(WilsonPrecontactSeparatedLamps.portion A.E (picked A.E reg)).Paid w P.p.B a M):
    (gallery c reg use A).Pays w a (e+‖c‖*M) (max 1 ‖c‖*k):=
  ⟨regular _ reg c hw all.budget small,forced _ use c all.wages⟩

end YM.Integration.WilsonThermometerMixedShoulder
