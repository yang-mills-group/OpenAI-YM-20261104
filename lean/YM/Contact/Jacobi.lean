import YM.Contact.Trial

/-! Relative Jacobi coordinates (orthonormal for the Euclidean positions) at a collapsing
arity, and the centroid map. The mean maps also on arity zero (zero to avoid partial choices).
For the orthogonal change of variables use only positive arities; normal volume there is full
Lebesgue volume on `Points k`, where `k+1` is the arity. -/

noncomputable section
set_option autoImplicit false
open LinearMap Function Set Filter MeasureTheory
open scoped BigOperators ContDiff InnerProductSpace Topology
namespace YM.Contacts

variable (n:ℕ)

def tally : Points n →ₗ[ℝ] E4:= ∑ i:Fin n,(PiLp.proj 2 (fun _ :Fin n=>E4) i).toLinearMap

def diagonal : E4→ₗ[ℝ] Points n where
  toFun x:= points fun _=>x
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def centroid : Points n →ₗ[ℝ] E4:= (n:ℝ)⁻¹ • tally n

def residual : Points n →ₗ[ℝ] Points n:= LinearMap.id - (diagonal n).comp (centroid n)

@[simp]
lemma tally_apply (x:Points n): tally n x=∑ i,x i:=by simp [tally,LinearMap.sum_apply]
@[simp]
lemma diagonal_apply (x:E4) (i:Fin n):diagonal n x i=x:=rfl
@[simp]
lemma centroid_apply (x:Points n):centroid n x=(n:ℝ)⁻¹ • ∑ i,x i:=by simp [centroid]

lemma centroid_diagonal (hn:n≠0)(x:E4): centroid n (diagonal n x)=x:=by
   rw [centroid_apply,show (WithLp.ofLp (diagonal n x))=(fun _=>x) from rfl, Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀]
   · exact_mod_cast hn

lemma residual_ker (hn:n≠0)(x:Points n): residual n x ∈ LinearMap.ker (centroid n):=by
  rw [LinearMap.mem_ker]; change centroid n (x-_)=0; rw [map_sub,LinearMap.comp_apply,centroid_diagonal n hn,sub_self]

lemma relative_rank : Module.finrank ℝ (LinearMap.ker (centroid (n+1)))=Module.finrank ℝ (Points n):=by
  have hv:= (centroid (n+1)).finrank_range_add_finrank_ker
  have hr:(centroid (n+1)).range= ⊤:=LinearMap.range_eq_top.mpr (fun x=> ⟨_,centroid_diagonal (n+1) n.succ_ne_zero x⟩)
  rw [hr,finrank_top] at hv
  have hf(k:ℕ) : Module.finrank ℝ (Points k)=4*k:= by rw [Points.flatten.toLinearEquiv.finrank_eq]; simp [Axis,Nat.mul_comm]
  rw [show Module.finrank ℝ E4=4 by simp [E4,Axis],hf] at hv
  rw [hf];omega

/-- Some fixed orthonormal identification of the kernel of the mean coordinate with `4n`
dimensions. Thus Jacobi coordinates need not make arbitrary slot choices in defining the radius.
-/
def stair : Points n ≃ₗᵢ[ℝ] (LinearMap.ker (centroid (n+1))) :=
  let f : EuclideanSpace ℝ (Fin (Module.finrank ℝ (Points n))) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (LinearMap.ker (centroid (n+1))))) := (relative_rank n) ▸ LinearIsometryEquiv.refl ..
  (((stdOrthonormalBasis ℝ (Points n)).repr.trans f).trans (stdOrthonormalBasis ℝ (LinearMap.ker (centroid (n+1)))).repr.symm)

def differences (x:Points n) : Points (n+1) := (stair n x).val

def jacobi (x:Points (n+1)):= (stair n).symm ⟨residual (n+1) x,residual_ker (n+1) n.succ_ne_zero x⟩

lemma recenter (x:Points (n+1)):differences n (jacobi n x)=residual (n+1) x:=by
  dsimp only [differences,jacobi]; rw [LinearIsometryEquiv.apply_symm_apply]
lemma centered (y:Points n):centroid (n+1) (differences n y)=0:= (stair n y).property
lemma centered_sub (x:Points (n+1))(i j:Fin (n+1)):
     x i-x j=differences n (jacobi n x) i - differences n (jacobi n x) j:=by
  rw [recenter]; change _=x i-centroid _ _ -(x j-centroid _ _);abel

def gen (x:E4)(v:Points n):=diagonal (n+1) x+differences n v
@[simp] lemma center_gen (x:E4)(v:Points n): centroid (n+1) (gen n x v)=x:=by rw [gen,map_add,centered,centroid_diagonal _ (by omega),add_zero]
@[simp] lemma jacobi_gen (x:E4)(v:Points n):jacobi n (gen n x v)=v:=by
  apply (stair n).injective;apply Subtype.val_injective; change differences n _=differences n _
  rw [recenter];change gen n x v-diagonal _ (centroid (n+1) (gen n x v))=differences n _
  rw [center_gen, gen]; abel
lemma gen_self (x:Points (n+1)): gen n (centroid _ x) (jacobi n x)=x:=by
   change diagonal _ _+_=x
   rw [recenter]; change _+(x-_)=x; rw [show (LinearMap.comp _ _) x=diagonal _ (centroid _ x) from rfl]; abel

lemma diagonal_norm_sq (x:E4) : ‖diagonal n x‖^2=n*‖x‖^2:=by rw [PiLp.norm_sq_eq_of_L2]; dsimp [diagonal]; simp

lemma norm_diff (x:Points n): ‖differences n x‖=‖x‖:=(stair n).norm_map ..
lemma norm_chart (x:Points (n+1)): ‖x‖^2= ‖Real.sqrt (n+1) • centroid _ x‖^2+‖jacobi n x‖^2:=by
  let u:= centroid (n+1) x; let y:= jacobi n x; let b:=differences n y
  have h_pyth:⟪diagonal (n+1) u,b⟫_ℝ=0:= calc
      _ = ∑ i,⟪u,b i⟫_ℝ := PiLp.inner_apply _ _
      _ = ⟪u,∑ i, b i⟫_ℝ:= (inner_sum ..).symm
      _ = 0 := by
        have hb:∑ i,b i=0:= (tally_apply (n+1) b) ▸ (show tally (n+1) b=0 from by
          rw [(show tally (n+1) b=((↑n+1):ℝ) • (centroid (n+1) b) from ?_), centered,smul_zero]
          simp [centroid_apply,show (n:ℝ)+1≠0 by positivity,smul_smul])
        rw [hb, inner_zero_right]
  nth_rewrite 1 [← gen_self n x]
  change ‖diagonal (n+1) u+b‖^2=‖Real.sqrt (n+1) • u‖^2+‖y‖^2
  rw [norm_add_sq_real, diagonal_norm_sq,h_pyth,norm_diff,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (show (0:ℝ)≤n+1 by positivity)]; simp

@[simp] lemma jacobi_zero: jacobi n 0=0:=by rw [show (0:Points (n+1))=gen n 0 0 by unfold gen differences; simp only [map_zero,zero_add];rfl, jacobi_gen]
@[simp] lemma jacobi_add (v w : Points (n+1)): jacobi n (v+w)=jacobi n v+jacobi n w:=by
   change (stair n).symm _=(stair n).symm _+ (stair n).symm _
   rw [← map_add]; congr 1; apply Subtype.ext;exact map_add (residual _) _ _
@[simp] lemma jacobi_smul (r:ℝ)(v:Points (n+1)):jacobi n (r • v)=r • jacobi n v:=by
   change (stair n).symm _=r • (stair n).symm _
   rw [← map_smul]; congr 1; apply Subtype.ext;exact (residual _).map_smul ..

def rootLen:ℝ:=Real.sqrt ((n:ℝ)+1)
lemma root_pos :0<rootLen n:=Real.sqrt_pos.mpr (by positivity)
lemma root_ne :rootLen n≠0:= (root_pos n).ne'
lemma norm_centroid (x:Points (n+1)) : ‖centroid _ x‖ ≤ (rootLen n)⁻¹*‖x‖:= by
   have := norm_chart n x
   rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at this
   change ‖x‖^2=(rootLen n * _)^2+_ at this
   rw [le_inv_mul_iff₀ (root_pos n)]
   nlinarith only [this,root_pos n,norm_nonneg x,norm_nonneg (centroid (n+1) x),sq_nonneg ‖jacobi n x‖]
lemma norm_relative (x:Points (n+1)): ‖jacobi n x‖ ≤ ‖x‖:= by nlinarith only [norm_chart n x,sq_nonneg ‖rootLen n • centroid _ x‖,norm_nonneg (jacobi n x),norm_nonneg x]

-- Orthogonal pair of center and differences, before changing from root-length units back to the actual centroid.
def isoChart : Points (n+1) ≃ₗᵢ[ℝ] WithLp 2 (E4 × Points n) where
   toFun x := WithLp.toLp 2 (rootLen n • centroid _ x,jacobi n x)
   invFun p:= gen n ((rootLen n)⁻¹ • p.fst) p.snd
   left_inv x:= by dsimp; rw [inv_smul_smul₀ (root_ne n),gen_self]
   right_inv p:=by dsimp; apply WithLp.ofLp_injective _;apply Prod.ext
                   · dsimp; rw [center_gen,smul_inv_smul₀ (root_ne _)]
                   exact jacobi_gen ..
   map_add' x y:=by apply WithLp.ofLp_injective _; apply Prod.ext
                    · change rootLen n • centroid _ (x+y)=rootLen n • centroid _ x+rootLen n • centroid _ y;rw [map_add,smul_add]
                    exact jacobi_add ..
   map_smul' r x:=by change WithLp.toLp _ _=r • _; apply WithLp.ofLp_injective _; apply Prod.ext
                     · change rootLen n • centroid _ (r•x)=r • rootLen n • centroid _ x;rw [map_smul];apply smul_comm
                     exact jacobi_smul ..
   norm_map' x:= (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [WithLp.prod_norm_sq_eq_of_L2,norm_chart];rfl)

-- `coordinates` is written using continuous-linear evaluation formulas; the center factor is
-- not normalized in uses below.
def coordinates : Points (n+1) ≃ₗ[ℝ] (E4 × Points n) where
  toFun x := (centroid _ x,jacobi _ x)
  invFun p := gen n p.1 p.2
  left_inv := gen_self _
  right_inv _:=Prod.ext (center_gen ..) (jacobi_gen ..)
  map_add' _ _:= Prod.ext (map_add ..) (jacobi_add ..)
  map_smul' _ _:= Prod.ext ((centroid _).map_smul ..) (jacobi_smul ..)
 
abbrev volumePower := rootLen n ^ 4
private def rescaleCenter: E4 × Points n ≃ₜ E4 × Points n:= (Homeomorph.smul (Units.mk0 (rootLen n)⁻¹ (inv_ne_zero (root_ne n)))).prodCongr (Homeomorph.refl _)
private def orthogonalChart: Points (n+1) ≃ₜ (E4 × Points n) := (isoChart n).toHomeomorph.trans (WithLp.homeomorphProd _ _ _)

lemma chart_formula(x:Points (n+1)): coordinates n x=(rescaleCenter n) ((orthogonalChart n) x):= by
   dsimp [coordinates,rescaleCenter,orthogonalChart,isoChart,LinearIsometryEquiv.toHomeomorph]; congr 1; exact (inv_smul_smul₀ (root_ne _) _).symm

private lemma center_map : Measure.map (rescaleCenter n) volume= ENNReal.ofReal (volumePower n) • volume:=by
   have ht:= (volume:Measure E4).map_addHaar_smul (inv_ne_zero (root_ne n)); rw [inv_pow, inv_inv,
     (show Module.finrank ℝ E4=4 by simp [E4,Axis]), abs_of_nonneg (by positivity : 0 ≤ volumePower n)] at ht
   let B:ENNReal := ENNReal.ofReal (volumePower n)
   let C (x:E4):= (rootLen n)⁻¹ • x
   change Measure.map C volume = B • volume at ht
   change Measure.map (Prod.map C id) ((volume:Measure E4).prod (volume:Measure (Points n)))=B • (volume:Measure E4).prod volume
   rw [← Measure.map_prod_map _ _ (show Measurable C from continuous_id.const_smul (rootLen n)⁻¹|>.measurable) measurable_id, ht,Measure.map_id,Measure.prod_smul_left]

lemma preserves_jacobi: Measure.map (coordinates n) volume= ENNReal.ofReal (volumePower n) • volume:=by
    have h_orth: Measure.map (orthogonalChart n) volume=volume:=
       (WithLp.volume_preserving_ofLp E4 (Points n)|>.comp (LinearIsometryEquiv.measurePreserving (isoChart n))).map_eq
    rw [show ⇑(coordinates n)=rescaleCenter n ∘ orthogonalChart n from funext (chart_formula n)]
    rw [← Measure.map_map (rescaleCenter n).measurable ((orthogonalChart n).measurable), h_orth,center_map]

lemma jacobi_integral {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F](f: E4×Points n→ F):
   (rootLen n)^4 • (∫ p, f p)=∫ x,f (centroid _ x,jacobi n x):=by
  let C:= (orthogonalChart n|>.trans (rescaleCenter n)).toMeasurableEquiv
  rw [show (fun x=>f (centroid _ x,jacobi n x))=(fun x=> f (C x)) from funext fun x=>congr_arg f (chart_formula n x), ← integral_map_equiv]
  rw [show Measure.map C (volume:Measure (Points (n+1)))=Measure.map (coordinates n) volume from congr_arg (fun z=>Measure.map z _) (funext (fun x=>(chart_formula n x).symm)), preserves_jacobi, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
lemma jacobi_integral' {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F](f: Points (n+1)→ F):
  ∫ x,f x=(rootLen n)^4 • (∫ p:E4×Points n, f (gen n p.1 p.2)):=by
  rw [jacobi_integral];simp_rw [gen_self]

end YM.Contacts
