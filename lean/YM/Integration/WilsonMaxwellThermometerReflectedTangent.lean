import YM.Integration.WilsonMaxwellThermometerReflectedCalibration
import YM.Integration.WilsonMaxwellThermometerFiniteTangent

/-! Insert the actual fitted occupied lower component into the complete
finite three-field credit on the same independent board. All genuine
proper faces and the two original equivariant shoulders are retained. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedTangent
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Maxwell
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Source Source.Drops Labels XSpace XSpace.Normalize XSpace.Cirrus XSpace.Rose XSpace.Structure1
open XSpace.Photo XSpace.Tornado XSpace.Retirement Table.Pairing
open WilsonMaxwellThermometerLowerPointGram (occupied)
open WilsonMaxwellThermometerLowerFiledGram (field)
open WilsonMaxwellThermometerLowerGramPrice (Index token reassemble)
open private basis from YM.Integration.WilsonMaxwellThermometerLowerGramPrice
open WilsonMaxwellThermometerIndependentReflection (panel)
open WilsonMaxwellThermometerReflectedScalar (connected)
open WilsonMaxwellThermometerReflectedFirstPrice (filed)
open WilsonMaxwellThermometerReflectedIncidence (Gram Pair mass site)
open WilsonMaxwellThermometerFiniteTangent (credit cost roster)
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Classical BigOperators Topology
variable {G:Gauge}(a:Axis)(x:E4)
def raised :occupied G a x→ₗ[ℂ] Sec G 6 where
  toFun z:=up (by decide:4≤6) (field a x z)
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private theorem salary {I:Type} [Fintype I](B:Module.Basis I ℂ (Sec G 6)):
    ∃D:ℝ,0≤D ∧ ∀z:occupied G a x, (∑i:I,‖B.repr (raised a x z) i‖) ≤ D*‖token a x z‖:=by
  let f:=Module.finBasis ℂ (occupied G a x)
  let A (i:I)(j:Index G a x):=B.repr (raised a x (f j)) i
  let D:=∑i:I,∑j:Index G a x,‖A i j‖
  refine ⟨D,sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>norm_nonneg _)),?_⟩
  intro z
  have view (i:I):B.repr (raised a x z) i=∑j,token a x z j*A i j:=by
    have repr:=congrArg (fun t=>B.repr (raised a x t) i) (f.sum_repr z)
    simpa only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
      token,basis,Module.Basis.equivFun_apply,A,f] using repr.symm
  calc
    _ ≤ ∑i:I,∑j:Index G a x,‖A i j‖*‖token a x z‖:=by
      refine sum_le_sum fun i _=>?_
      rw [view]
      apply (norm_sum_le ..).trans
      apply sum_le_sum;intro j _
      rw [norm_mul,mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm _ j) (norm_nonneg _)
    _ = _:=by simp only [D,Finset.sum_mul]

theorem ground (W:Initialize G){V:Store G}(K:Pick V)(simple:G.Simple)
    (P Q:Module.End ℂ (Sec G 4))(hP:Equivariant P)(hQ:Equivariant Q):
    ∃C:ℝ,0≤C ∧ ∀ᶠ M in Front,∀z:occupied G a x,
      ‖credit W K M (raised a x z) (P (lower G)) (Q (lower G))‖ ≤ C*M.spacing*‖token a x z‖:=by
  let f:=Module.finBasis ℂ (Sec G 6)
  obtain ⟨C,hC,fee⟩:=WilsonMaxwellThermometerFiniteTangent.full W K f
  obtain ⟨D,hD,owns⟩:=salary a x f
  let α (p:Sec G 4):=∑i,‖f.repr (up (by decide:4≤6) p) i‖
  let p:=P (lower G); let q:=Q (lower G)
  have ap:0≤α p:=sum_nonneg fun _ _=>norm_nonneg _
  have aq:0≤α q:=sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨C*D*α p*α q,by positivity,?_⟩
  filter_upwards [fee] with M earned
  intro z
  have observed:=earned (raised a x z) p q
  rw [WilsonMaxwellThermometerCommonTangent.separate K simple _ _ _ hP hQ,sub_zero] at observed
  have measure:cost f (roster (raised a x z) p q)= (∑i,‖f.repr (raised a x z) i‖)*(α p)*(α q):=by
    change (∏j:Fin 3,∑i,‖f.repr (roster (raised a x z) p q j) i‖)=_
    rw [Fin.prod_univ_three];rfl
  rw [measure] at observed
  calc
    _ ≤ C*M.spacing*((∑i,‖f.repr (raised a x z) i‖)*α p*α q):=observed
    _ ≤ C*M.spacing*((D*‖token a x z‖)*α p*α q):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (owns z) ap) aq) (mul_nonneg hC M.positive.le)
    _ = _:=by ring

theorem decay (U:XSpace.Run)(p:ℕ):
    Tendsto (fun n:ℕ=>(U.step n).spacing*(1+(n:ℝ))^p) atTop (𝓝 0):=by
  have hp:1<(U.ratio:ℝ):=by have h:=U.large;exact_mod_cast (show 1<U.ratio by omega)
  have hr:Tendsto (fun n:ℕ=>(((n+1:ℕ):ℝ)^p)/(U.ratio:ℝ)^(n+1)) atTop (𝓝 0):=
    (tendsto_pow_const_div_const_pow_of_one_lt p hp).comp (tendsto_add_atTop_nat 1)
  have h:=hr.const_mul (U.ratio:ℝ)
  rw [mul_zero] at h
  apply h.congr
  intro n
  change (U.ratio:ℝ)*(((n+1:ℕ):ℝ)^p/(U.ratio:ℝ)^(n+1))=
    ((U.ratio^n:ℕ):ℝ)⁻¹*(1+(n:ℝ))^p
  push_cast
  rw [pow_succ,add_comm (n:ℝ) 1]
  field_simp

end YM.Integration.WilsonMaxwellThermometerReflectedTangent
