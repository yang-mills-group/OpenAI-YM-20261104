import YM.Integration.WilsonOriginalCompoundLodge
import YM.Integration.WilsonMarkedInheritedGaussianKernel
import YM.Integration.WilsonFiniteMarkedWickDiagonal

/-! An actual Wick pair removes two field coordinates. Its coefficient is paid on the original finite forest, independently of the number of sites. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakPair
open Function Finset Lattice Laurent Bloch Precision RG Next.Free Work.F08 FormalBulk08 Flat Stationary
open AllOrder AllOrder.Floe Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open scoped Classical BigOperators
variable {G:Gauge} {U E:Type*} [Fintype U] [NormedAddCommGroup E]

def mass (w:U→ℝ) : (r:ℕ) → Ten E U r → ℝ
| 0,P => ‖P Fin.elim0‖
| r+1,P => ∑a:U,w a * mass w r (prune P a)

private theorem nonnegative (w:U→ℝ)(hp:∀a,0 ≤ w a)(r:ℕ)(P:Ten E U r):0 ≤ mass w r P:=by
  induction r with
  | zero => exact norm_nonneg _
  | succ r h => exact sum_nonneg fun a _=>mul_nonneg (hp a) (h _)

private theorem empty (w:U→ℝ)(r:ℕ):mass w r (0:Ten E U r)=0:=by
  induction r with
  | zero => exact norm_zero
  | succ r ih => simp [mass,show ∀a:U,prune (0:Ten E U (r+1)) a=0 from fun _=>rfl,ih]

private theorem append (w:U→ℝ)(hp:∀a,0 ≤ w a)(r:ℕ)(P Q:Ten E U r):
    mass w r (P+Q) ≤ mass w r P+mass w r Q:=by
  induction r with
  | zero => exact norm_add_le _ _
  | succ r ih =>
    simp only [mass,←sum_add_distrib,←mul_add]
    exact sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (ih (prune P a) (prune Q a)) (hp a)

variable [NormedSpace ℝ E]

private theorem scale (w:U→ℝ)(r:ℕ)(x:ℝ)(P:Ten E U r):mass w r (x • P)=|x| * mass w r P:=by
  induction r with
  | zero => exact norm_smul x (P Fin.elim0)
  | succ r ih =>
    have h (a:U):prune (x • P) a=x • prune P a:=rfl
    simp only [mass,h,ih,mul_sum]
    apply sum_congr rfl;intro a _;ring

omit [NormedSpace ℝ E] in
private theorem add_up {ι:Type*}(w:U→ℝ)(hp:∀a,0 ≤ w a)(r:ℕ)(s:Finset ι)(F:ι→Ten E U r):
    mass w r (∑i∈s,F i) ≤ ∑i∈s,mass w r (F i):=by
  induction s using Finset.induction_on with
  | empty => simp [empty]
  | insert a s ha ih => simp only [sum_insert ha];exact (append w hp r _ _).trans (add_le_add_right ih _)

theorem booked (w:U→ℝ)(hp:∀u,1 ≤ w u)(C:Matrix U U ℝ)(B:ℝ)(c:∀a b,|C a b| ≤ B)
    (r:ℕ)(P:Gen E U):
    mass w r (ripple C P r)  ≤  ((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)*(B/2)*mass w (r+2) (P (r+2)):=by
  let m:ℝ:=((r+1:ℕ):ℝ)*((r+2:ℕ):ℝ)
  have mp:0 ≤ m:=by dsimp [m];positivity
  have wp (u:U):0 ≤ w u:=(hp u).trans' zero_le_one
  let old (a b:U):=mass w r (prune (prune (P (r+2)) b) a)
  have live (a b:U):0 ≤ old a b:=nonnegative w wp r _
  have split:ripple C P r=∑a:U,∑b:U,(C a b/2*m) • (prune (prune (P (r+2)) b) a):=by
    ext x
    simp only [Blue.ripple,Finset.sum_apply,Pi.smul_apply,sever,prune]
    apply sum_congr rfl;intro a _
    apply sum_congr rfl;intro b _
    simp only [←Nat.cast_smul_eq_nsmul ℝ,smul_smul]
    congr 1
  rw [split]
  calc
    _  ≤  ∑a:U,∑b:U,|C a b/2*m| * old a b :=by
        refine (add_up w wp r univ _).trans (sum_le_sum fun a _=>?_ )
        exact (add_up w wp r univ _).trans_eq (by simp only [scale,old])
    _  ≤  ∑a:U,∑b:U,m*(B/2)*(w b*(w a*old a b)) :=by
        refine sum_le_sum fun a _=>sum_le_sum fun b _=>?_
        rw [abs_mul,abs_of_nonneg mp,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
        have step₀: |C a b| / 2*m  ≤  m*(B/2):=by nlinarith only [mul_nonneg (sub_nonneg.mpr (c a b)) mp]
        have l:old a b ≤ w a*old a b:=le_mul_of_one_le_left (live a b) (hp a)
        have l':w a*old a b ≤ w b*(w a*old a b):=le_mul_of_one_le_left (mul_nonneg (wp _) (live a b)) (hp b)
        exact mul_le_mul step₀ (l.trans l') (live a b) (mul_nonneg mp (div_nonneg ((abs_nonneg _).trans (c a b)) (by norm_num)))
    _ = _ :=by rw [sum_comm];simp only [mass,mul_sum,m,old]

variable (R:Run G) (fund:WilsonOriginalCompoundLodge.Filed R.kit) (i:ℕ)(ht:4 ≤ R.alloy.B.a.clock.J i)

include fund ht in
theorem original :
    let A:=R.alloy.B.a
    let K:=R.metals.p.kernel
    let X:Patch:=(A.clock.op i 0).patch
    ∀F:Lodge X,∃c:ℝ,0<c ∧ c ≤ Borough.ageZ (A.clock.hatBeta i) ∧
      ∀N M:ℕ,i<N → N ≤ M → ∀hh:X.Branches K G,∀n:Side,
        let P:=destination A N i
        ∀a b,|(Reef.ferry P hh F n).saddle.q a b| ≤ c:=by
  intro A K X F
  obtain ⟨c,cp,cost,all⟩:=WilsonOriginalCompoundLodge.figure R fund i ht F
  refine ⟨c,cp,cost,?_⟩
  intro N M iN NM hh n P a b
  let s:=F.splitting (G:=G) (S:=Flat.primary P.patch K n)
  change |(Flat.gamma G K P F hh).acts n (s a) (s b)| ≤ c
  apply WilsonMarkedInheritedGaussianKernel.folded _ _ (all N M iN NM hh).1
  exact (WilsonThermometerUnitFilingWeakRoom.book G K X.J (A.clock.J i)).width_pos.le

end YM.Integration.WilsonThermometerUnitFilingWeakPair
