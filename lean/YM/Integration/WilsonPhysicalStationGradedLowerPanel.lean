import YM.Integration.WilsonPhysicalStationLowerDual
import YM.Integration.WilsonPhysicalNamedVaneBasis

/-! The earlier basis is chosen inside its own measured chart. Its free reflected basis is
turned before applying that chart, so testing all pivots spans the physical lower space
without imposing compatibility between two distinct engineering horizons. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationGradedLowerPanel
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonPhysicalStationLowerReceiver (ear)
open WilsonPositionProgramPublicWickGram (reading nodes)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (U:tower S)(B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "C₀" => Bel R.family.book

def left (i:I):S.Field e:=U e ((C₀).adj (Maxwell.Free.spin_free R.family.labels) e a (named R B e i))
def right (j:I):S.Field e:=U e (named R B e j)
def frame (x:Points 2):Matrix I I ℂ:=fun i j=>ear R x (right R U B e j) (left R U B e a i)

/-- Each tested basis vector is deposited through the original coarse chart at grade e. -/
theorem complete (L M:S.Field e→ₗ[ℂ]ℂ)(observed:∀i:I,L (left R U B e a i)=M (left R U B e a i)):L=M:=by
  let turn:=(C₀).adj (Maxwell.Free.spin_free R.family.labels) e a
  have same:(L.comp (U e).toLinearMap).comp turn=(M.comp (U e).toLinearMap).comp turn:=
    (named R B e).ext fun i=>observed i
  apply LinearMap.ext
  intro X
  have known:=DFunLike.congr_fun same (turn ((U e).symm X))
  simpa only [LinearMap.comp_apply,turn,Table.reflect_twice,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using known

def factor (T:ℝ)(i:I):ℂ:=(T:ℂ)^i.2.1.val

def metered (T:ℝ)(X:Matrix I I ℂ):Matrix I I ℂ:=
  fun i j=>X i j*(factor B e T j/factor B e T i)

def cross (T:ℝ)(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ):I→ℂ:=
  fun i=>(T:ℂ)^Q/factor B e T i*L (left R U B e a i)

def charge (x:Points 2)(T:ℝ)(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ):I→ℂ:=
  fun i=>factor B e T i/(T:ℂ)^Q*((metered B e T (frame R U B e a x))⁻¹ *ᵥ cross R U B e a T Q L) i

private theorem funded {T:ℝ}(pos:0<T)(i:I):factor B e T i≠0:=by
  unfold factor
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr pos.ne')

theorem solves (x:Points 2)(T:ℝ)(tp:0<T)(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ)
    (unit:IsUnit (metered B e T (frame R U B e a x)).det):
    ∑j:I,charge R U B e a x T Q L j • ear R (e:=e) x (right R U B e j)=L:=by
  apply complete R U B e a
  intro i
  let G₀:=frame R U B e a x
  let H:=metered B e T G₀
  let b:=cross R U B e a T Q L
  let v:=H⁻¹ *ᵥ b
  have eq:(H*ᵥv) i=b i:=by
    change (H*ᵥ(H⁻¹*ᵥb)) i=_
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ unit,Matrix.one_mulVec]
  have signal:(T:ℂ)^Q≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr tp.ne')
  have restored:=congrArg (fun t:ℂ=>factor B e T i/(T:ℂ)^Q*t) eq
  change factor B e T i/(T:ℂ)^Q*(∑j:I,H i j*v j)=factor B e T i/(T:ℂ)^Q*((T:ℂ)^Q/factor B e T i*L (left R U B e a i)) at restored
  rw [show factor B e T i/(T:ℂ)^Q*((T:ℂ)^Q/factor B e T i*L (left R U B e a i))=L (left R U B e a i) by field_simp [funded B e tp i,signal],Finset.mul_sum] at restored
  rw [←restored]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  change (factor B e T j/(T:ℂ)^Q*v j)*G₀ i j=factor B e T i/(T:ℂ)^Q*((G₀ i j*(factor B e T j/factor B e T i))*v j)
  field_simp [funded B e tp i,signal]

/-- One tolerance at the original free positive matrix controls the entire normalized inverse
on the genuine coarse lower panel, before the target or its rank is chosen. -/
theorem original :
    ∃δ K:ℝ,0<δ ∧ 0<K ∧ ∀(x:Points 2)(T:ℝ),0<T→
      ‖(fun i j:I=>metered B e T (frame R U B e a x) i j)-reading a (nodes a) (id:I→I)‖≤δ→
      ∀(Q:ℕ)(L:S.Field e→ₗ[ℂ]ℂ),
        (∑j:I,charge R U B e a x T Q L j • ear R (e:=e) x (right R U B e j)=L) ∧
        ∀j:I,‖charge R U B e a x T Q L j‖*T^Q ≤ T^j.2.1.val*K*‖cross R U B e a T Q L‖:=by
  obtain ⟨k,δ,kp,dp,grant⟩:=WilsonOriginalPublicRelativeGramReference.original a (id:I→I) Function.injective_id
  let cap:ℝ:=∑_i:I,∑_j:I,(Fintype.card I:ℝ)/k
  have positive:0≤cap:=by dsimp [cap]; positivity
  refine ⟨δ,cap+1,dp,by linarith,?_⟩
  intro x T tp near Q L
  let H:=metered B e T (frame R U B e a x)
  let b:=cross R U B e a T Q L
  obtain ⟨unit,small⟩:=grant H near
  refine ⟨solves R U B e a x T tp Q L unit,?_⟩
  intro j
  have bounded:= (norm_le_pi_norm (H⁻¹*ᵥ b) j).trans ((Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right small (norm_nonneg b)))
  have one:‖factor B e T j‖=T^j.2.1.val:=by simp [factor,Complex.norm_real,Real.norm_eq_abs,abs_of_pos tp]
  have sig:‖(T:ℂ)^Q‖=T^Q:=by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos tp]
  rw [charge,norm_mul,norm_div,one,sig]
  calc
    _ = T^j.2.1.val*‖(H⁻¹*ᵥ b) j‖ := by field_simp; rfl
    _ ≤ T^j.2.1.val*(cap*‖b‖):=mul_le_mul_of_nonneg_left bounded (pow_nonneg tp.le _)
    _ ≤ T^j.2.1.val*(cap+1)*‖b‖:=by rw [mul_assoc]; gcongr; linarith

end YM.Integration.WilsonPhysicalStationGradedLowerPanel
end
