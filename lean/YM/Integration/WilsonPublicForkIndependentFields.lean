import YM.Integration.WilsonPublicForkIndependentHearing

/-! The two independently prescribed ordinary readings for complete incoming
and reflected fields, expressed in the same public basis as the physical decoder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentFields
open Filter Function Set Finset MeasureTheory PowerSeries FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open FVA2.O.Project FVA2.Scale FVA2.Register Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater MS.Rake RG17 PhysMS Trace.Pilot
open WilsonMSDictionaryFarRead WilsonMSDictionaryVector WilsonPublicForkIndependentPlacement
open scoped Classical Topology BigOperators
variable {G:Gauge}(C:Family G){n:ℕ}(d:Fin n→ℕ)(h:ℕ)
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

abbrev Modes:=∀i:Fin n,Dframe.Toon G (d i)
def load (v:∀i,Free C (d i))(j:Modes (G:=G) d):ℂ:=∏i,(WilsonMSDictionaryVector.basis C (d i)).repr (v i) (j i)
def nearDose (v:∀i,Free C (d i)):ℝ:=∑j,‖load C d v j‖
def farDose (v:Free C h):ℝ:=∑k,‖(WilsonMSDictionaryVector.basis C h).repr v k‖
def unitScan (j:Dframe.Toon G h):Scan G 1:=fun _=>Dframe.flash j

theorem coordinate (v:∀i,Free C (d i))(coefficients:Modes (G:=G) d→Dframe.Toon G h→ℂ)(k:Dframe.Toon G h):
    (WilsonMSDictionaryVector.basis C h).repr (assemble C d h v coefficients) k=∑j,load C d v j*coefficients j k:=by
  change (WilsonMSDictionaryVector.basis C h).coord k (assemble C d h v coefficients)=_
  simp [assemble,load,Module.Basis.coord_apply,Finsupp.single_apply,mul_ite]

private theorem transport {E H:Type}[Fintype E][Fintype H](a:E→ℂ)(c:E→H→ℂ)(g:H→ℂ):
    (∑k,(∑j,a j*c j k)*g k)=∑j,a j*(∑k,c j k*g k):=by
  simp only [Finset.sum_mul,Finset.mul_sum];rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro j _;apply Finset.sum_congr rfl;intro k _;ring

private theorem outside {E H:Type}[Fintype E][Fintype H](c:E→ℂ)(b:H→ℂ)(g:H→E→ℂ):
    (∑k,c k*(∑u,b u*g u k))=∑u,b u*(∑k,c k*g u k):=by
  simp only [Finset.mul_sum];rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro j _;apply Finset.sum_congr rfl;intro k _;ring

def gram (q:ℕ)(z s:ℝ)(a:Free C h)(φ:Test 2)(k:Dframe.Toon G h):ℂ:=
  ∑u,(WilsonMSDictionaryVector.basis C h).repr a u*WilsonPublicForkIndependentHearing.two Z q z s (unitScan h u) k φ

def full (q:ℕ)(z s:ℝ)(v:∀i,Free C (d i))(a:Free C h)(ψ:Test n)(φ:Test 2):ℂ:=
  ∑j,load C d v j*(∑u,(WilsonMSDictionaryVector.basis C h).repr a u*WilsonPublicForkIndependentHearing.ordinary Z q z s
      (fun i=>Dframe.flash (j i)) (unitScan h u) ψ φ)

include ν ms in
theorem original (g:ℝ→ℝ)(physical:Coupling G g)(q P A:ℕ)(reserve:P<A)(order:P+A*(2*h+1)<q+1)
    (K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)(φ:Test 2):
    ∀ᶠ r in trail,∀(v:∀i,Free C (d i))(a:Free C h)(ψ:Test n),tsupport ψ⊆K →
      ‖full C d h Z q (g r) (age A (g r)) v a ψ φ-
        ∑k,(WilsonMSDictionaryVector.basis C h).repr (prediction C d h Z M ν v ψ q (g r)) k*gram C h Z q (g r) (age A (g r)) a φ k‖≤
        nearDose C d v*farDose C h a*Read.Value ψ*Read.Value φ*(g r)^(P+A*(2*h+1)):=by
  have modes:∀ᶠ r in trail,∀ (j:Modes (G:=G) d) (u:Dframe.Toon G h) (ψ:Test n),tsupport ψ⊆K →
      ‖WilsonPublicForkIndependentHearing.ordinary Z q (g r) (age A (g r)) (fun i=>Dframe.flash (j i)) (unitScan h u) ψ φ-
        ∑b:Dframe.Toon G h,cutoff q (g r) (converted Z M ν (fun i=>Dframe.flash (j i)) ψ (Dframe.flash b))*
        WilsonPublicForkIndependentHearing.two Z q (g r) (age A (g r)) (unitScan h u) b φ‖≤
        Read.Value ψ*Read.Value φ*(g r)^(P+A*(2*h+1)):=by
    apply eventually_all.mpr;intro j;apply eventually_all.mpr;intro u
    exact WilsonPublicForkIndependentHearing.original Z M ν ms g physical h q P A reserve order _ _ K closed inside φ
  filter_upwards [modes] with r paid v a ψ allowed
  let c:=fun (j:Modes (G:=G) d)(k:Dframe.Toon G h)=>cutoff q (g r) (converted Z M ν (fun i=>Dframe.flash (j i)) ψ (Dframe.flash k))
  let b: Dframe.Toon G h→ℂ:=fun u=>(WilsonMSDictionaryVector.basis C h).repr a u
  let f:=fun (j:Modes (G:=G) d)(u:Dframe.Toon G h)=>WilsonPublicForkIndependentHearing.ordinary Z q (g r) (age A (g r)) (fun i=>Dframe.flash (j i)) (unitScan h u) ψ φ
  let k:=fun (u l:Dframe.Toon G h)=>WilsonPublicForkIndependentHearing.two Z q (g r) (age A (g r)) (unitScan h u) l φ
  let cost:=Read.Value ψ*Read.Value φ*(g r)^(P+A*(2*h+1))
  have total(j:Modes (G:=G) d):‖∑u,b u*(f j u-∑l,c j l*k u l)‖≤(farDose C h a)*cost:=by
    refine (norm_sum_le _ _).trans ?_
    rw [farDose,Finset.sum_mul]
    exact Finset.sum_le_sum fun u _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (paid j u ψ allowed) (norm_nonneg _)
  have allTerms:‖∑j,load C d v j*(∑u,b u*(f j u-∑l,c j l*k u l))‖≤
      nearDose C d v*((farDose C h a)*cost):=by
    refine (norm_sum_le _ _).trans ?_
    rw [nearDose,Finset.sum_mul]
    exact Finset.sum_le_sum fun j _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (total j) (norm_nonneg _)
  have axes(l:Dframe.Toon G h):(WilsonMSDictionaryVector.basis C h).repr (prediction C d h Z M ν v ψ q (g r)) l=
      ∑j,load C d v j*c j l:=coordinate C d h v c l
  simp_rw [axes]
  change ‖(∑j,load C d v j*(∑u,b u*f j u))-(∑l,(∑j,load C d v j*c j l)*(∑u,b u*k u l))‖≤_
  rw [transport]
  have reorganize(j:Modes (G:=G) d):(∑l,c j l*(∑u,b u*k u l))=∑u,b u*(∑l,c j l*k u l):=outside (c j) b k
  simp_rw [reorganize]
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub,←Finset.sum_sub_distrib,←mul_sub]
  exact allTerms.trans_eq (by dsimp only [cost];ring)

theorem budget :
    ∃(D:ℝ),0≤D ∧ ∀(v:∀i,Free C (d i))(a:Free C h),
      nearDose C d v*farDose C h a≤D*(∏i,‖v i‖)*‖a‖:=by
  let weights:=fun j:Modes (G:=G) d=>∏i,‖((WilsonMSDictionaryVector.basis C (d i)).coord (j i)).toContinuousLinearMap‖
  let head:=∑j:Modes (G:=G) d,weights j
  let tail:=∑k:Dframe.Toon G h,‖((WilsonMSDictionaryVector.basis C h).coord k).toContinuousLinearMap‖
  have hp:0≤head:=Finset.sum_nonneg fun j _=>Finset.prod_nonneg fun i _=>((WilsonMSDictionaryVector.basis C (d i)).coord (j i)).toContinuousLinearMap.opNorm_nonneg
  have tp:0≤tail:=Finset.sum_nonneg fun k _=>((WilsonMSDictionaryVector.basis C h).coord k).toContinuousLinearMap.opNorm_nonneg
  refine ⟨head*tail,mul_nonneg hp tp,?_⟩
  intro v a
  have nn:nearDose C d v≤head*∏i,‖v i‖:=by
    dsimp only [nearDose,head,load];rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _=>?_
    rw [norm_prod,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) fun i _=>((WilsonMSDictionaryVector.basis C (d i)).coord (j i)).toContinuousLinearMap.le_opNorm _
  have ff:farDose C h a≤tail*‖a‖:=by
    dsimp only [farDose,tail];rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _=>((WilsonMSDictionaryVector.basis C h).coord k).toContinuousLinearMap.le_opNorm _
  exact (mul_le_mul nn ff (Finset.sum_nonneg fun _ _=>norm_nonneg _) (mul_nonneg hp (Finset.prod_nonneg fun _ _=>norm_nonneg _))).trans_eq (by ring)

end YM.Integration.WilsonPublicForkIndependentFields
