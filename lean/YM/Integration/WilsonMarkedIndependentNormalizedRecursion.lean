import YM.Integration.WilsonMarkedIndependentNormalizedTop
import YM.Integration.WilsonMarkedIndependentNormalizedSeam
import YM.Integration.WilsonMarkedIndependentFiniteVectorSlope

/-! The full one-label log reduces to its normalized conditional integral.
Folding commutes with every stored subcell summation and marked linear map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentNormalizedRecursion
open Function Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι→ℕ}

theorem singleton (A:Levels G)(O:ChartRatio G)(m N:ℕ)(live:m<N)(simple:G.Simple)(good:LocalRatio O)
    (E:family G D)(law:Eu k E)(vac:E ∅=0)(s:ι):
    logO A O m N E k {s}=verseI A O m N (mass k {s}) (E {s}):=by
  have he:=congrFun (step_S A O m N E k live simple good law) {s}
  rw [levSingle (logHush A O m N E k) (step_L A O m N E k live simple good law) s] at he
  simpa only [edV,levSingle vac law s] using he

theorem reversion {V U:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
    (C:Cost)(T H:Pal V U)(a r:ℕ)(M:ℝ)
    (paid:∀b≤a,∀x,‖T b r x-H b r x‖≤M)(x):
    ‖Blue.mix C T a r x-Blue.mix C H a r x‖≤rimJ C a r*M:=by
  classical
  let c(b:ℕ):=coeff (a-b) (C^b*(C⁻¹)^r)
  change ‖(∑b∈range (a+1),c b • T b r) x-(∑b∈range (a+1),c b • H b r) x‖
    ≤(∑b∈range (a+1),‖c b‖)*M
  simp only [Finset.sum_apply,Pi.smul_apply,←Finset.sum_sub_distrib,←smul_sub,Finset.sum_mul]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum fun b hb=>by rw [norm_smul];exact mul_le_mul_of_nonneg_left (paid b (Nat.le_of_lt_succ (mem_range.mp hb)) x) (norm_nonneg _)

private theorem sum_fold {J V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
    (F:J→Era G V)(c:ℕ)(S:Finset J)(legal:∀j∈S,Auth c (F j))(n:Side)(a r:ℕ):
    plume ((∑j∈S,F j).2 a r) n=∑j∈S,plume ((F j).2 a r) n:=by
  classical
  induction S using Finset.induction_on with
  | empty=>simp only [Finset.sum_empty];exact plume_zero ..
  | @insert j S out ih=>
    have inS:∀b∈S,Auth c (F b):=fun b hb=>legal b (mem_insert_of_mem hb)
    obtain ⟨s,A,hs,p⟩:=((legal j (mem_insert_self ..)).wing a r).land
    obtain ⟨t,B,ht,q⟩:=((Auth.sum inS).wing a r).land
    rw [Finset.sum_insert out,Finset.sum_insert out]
    change plume ((F j).2 a r+(∑b∈S,F b).2 a r) n=_
    rw [plume_add p q hs ht,ih inS]

/-- The entire finite subcell ensemble carries exactly its engineering factor.
The native dual map contracts even when the tested coefficient is a scalar. -/
theorem reindex (P:Patch)(K k:ι→ℕ)(X:Outerm G D)(well:Solo k X)(y:ι → Cover)(S:Finset ι)(n:Side)
    (i r:ℕ)(A:ℝ)(price:∀b:backRow P.L S,∀x,
      let Z:=X (splitQ P y S b) S
      ‖Z.1 n i r x-plume (Z.2 i r) n x‖≤A)(x):
    let Z:=unite P K X y S
    ‖Z.1 n i r x-plume (Z.2 i r) n x‖≤(P.L.val:ℝ)^mass K S*A:=by
  classical
  intro Z
  let Y(b:backRow P.L S):=X (splitQ P y S b) S
  let row (b:backRow P.L S):=portV P K X y S b
  let c:=scalesK P K S
  have hc:0≤c:=scalesBound ..
  have shift(b:backRow P.L S):‖(row b).1 n i r x-plume ((row b).2 i r) n x‖≤c*A:=by
    let L:=mend P (inflate P S b) D S
    obtain ⟨s,v,hs,cork⟩:=((well (splitQ P y S b) S).wing i r).land
    let M:=c • L
    have folded:plume ((row b).2 i r) n=M ∘ plume ((Y b).2 i r) n:=
      plume_map ((Y b).2 i r) cork hs M n
    rw [folded]
    change ‖M ((Y b).1 n i r x)-M (plume ((Y b).2 i r) n x)‖≤c*A
    rw [←map_sub]
    change ‖c • L ((Y b).1 n i r x-plume ((Y b).2 i r) n x)‖≤c*A
    rw [norm_smul,Real.norm_of_nonneg hc]
    apply mul_le_mul_of_nonneg_left _ hc
    apply (L.le_opNorm _).trans
    apply (mul_le_of_le_one_left (norm_nonneg _) (mend_norm ..)).trans
    exact price b x
  have folded:=sum_fold row (mass k S) univ (fun b _=>road P K X well y S b) n i r
  change ‖(∑b,row b).1 n i r x-plume ((∑b,row b).2 i r) n x‖≤_
  rw [folded,Prod.fst_sum]
  simp only [Finset.sum_apply,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _≤∑_b:backRow P.L S,c*A:=Finset.sum_le_sum (fun b _=>shift b)
    _=_:=by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,crossBill]

end YM.Integration.WilsonMarkedIndependentNormalizedRecursion
end
