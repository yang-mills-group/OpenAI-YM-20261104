import YM.Integration.WilsonMaxwellThermometerReflectedIncidence
import YM.Integration.WilsonIndependentFittedExteriorWheel
import YM.Integration.WilsonIndependentConditionedGramSpatialCourse

/-! Submit each half of the same recorded positive-time energy test to the
finite-order marked conditional program, in its Cartesian coordinates. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedGramBulbProfile
open Function Filter Set MeasureTheory Metric Lattice Wilson Maxwell XSpace XSpace.Cirrus
open Table.Pairing WilsonMaxwellThermometerReflectedIncidence
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Layout
open scoped Topology Classical ContDiff
variable {D:ℕ}

def singleLinear:Point4 ≃ₗ[ℝ] Points 1 where
  toFun z:=site (WithLp.toLp 2 z)
  invFun z:=(z 0).ofLp
  left_inv _:=rfl
  right_inv z:=by
    apply PiLp.ext
    intro i
    have eq:i=0:=Subsingleton.elim ..;subst i;rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def singleChart:Point4 ≃L[ℝ] Points 1 where
  toLinearEquiv:=singleLinear
  continuous_toFun:=(PiLp.continuous_toLp 2 (fun _:Fin 1=>E4)).comp
    (continuous_pi (fun _:Fin 1=>PiLp.continuous_toLp 2 (fun _:Axis=>ℝ)))
  continuous_invFun:=(PiLp.continuous_ofLp 2 (fun _:Axis=>ℝ)).comp (PiLp.continuous_apply 2 _ 0)

def flip (a:Axis):Point4 ≃L[ℝ] Point4:=
  LinearEquiv.toContinuousLinearEquiv
    { toFun:=fun z j=>if j=a then -(z j) else z j
      invFun:=fun z j=>if j=a then -(z j) else z j
      left_inv:=fun z=>by ext j; by_cases h:j=a <;> simp [h]
      right_inv:=fun z=>by ext j; by_cases h:j=a <;> simp [h]
      map_add':=fun z w=>by ext j; by_cases h:j=a <;> simp [h,add_comm]
      map_smul':=fun c z=>by ext j; by_cases h:j=a <;> simp [h] }

def chart (a:Axis)(reflected:Bool):Point4 ≃L[ℝ] Points 1:=
  if reflected then (flip a).trans singleChart else singleChart

theorem time (a:Axis)(z:Point4):
    chart a false z 0 a=z a ∧ chart a true z 0 a= -z a:=by
  refine ⟨rfl,?_⟩
  change (if a=a then -(z a) else z a)=_
  simp

theorem actual (a:Axis)(z:Point4):
    chart a false z=site (WithLp.toLp 2 z) ∧ chart a true z=site (ride a (WithLp.toLp 2 z)):=by
  refine ⟨rfl,?_⟩
  ext i j
  change (if j=a then -(z j) else z j)=(ride a (WithLp.toLp 2 z)) j
  by_cases h:j=a <;> simp [ride,h]

variable {a:Axis}{x:E4}(B:Bulb (site x) a)

def paper (D:ℕ)(side:Bool):Phrase D:=
  ⟨fun z=>B.r (chart a side z),((B.bump.contDiff_normed (μ:=volume)).comp (chart a side).contDiff).of_le
    (show (D:WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)⟩

theorem compact (D:ℕ)(side:Bool):HasCompactSupport (paper B D side).val:=
  (B.bump.hasCompactSupport_normed (μ:=volume)).comp_homeomorph (chart a side).toHomeomorph

def profile (D:ℕ)(side:Bool):Rarity D:=(scenery (paper B D side) (compact B D side)).choose

theorem printed (D:ℕ)(side:Bool):(profile B D side).ψ=paper B D side:=
  (scenery (paper B D side) (compact B D side)).choose_spec

theorem value (D:ℕ)(side:Bool)(z:Point4):(profile B D side).ψ.val z=B.r (chart a side z):=by
  rw [printed];rfl

theorem supported (D:ℕ)(side:Bool){z:Point4}(member:z∈tsupport (profile B D side).ψ.val):
    chart a side z ∈ tsupport B.bump:=by
  rw [printed] at member
  refine closure_minimal (s:=Function.support (paper B D side).val) ?_
    (isClosed_closure.preimage (chart a side).continuous) member
  intro p visible
  apply subset_closure
  rw [B.bump.support_eq,←B.bump.support_normed_eq (μ:=volume)]
  exact visible

theorem gap:∃g:ℝ,0<g ∧ ∀(D₁ D₂:ℕ),ClearDay (profile B D₁ true) (profile B D₂ false) g:=by
  obtain ⟨z,zone,bottom⟩:=(isCompact_closedBall (site x) B.bump.rOut).exists_isMinOn
    (nonempty_closedBall.mpr B.bump.rOut_pos.le) (f:=fun z:Points 1=>z 0 a) (by fun_prop)
  have rise:0<z 0 a:=(B.active z (by rwa [B.bump.tsupport_eq])).2 0
  refine ⟨2*(z 0 a),by positivity,?_⟩
  intro D₁ D₂ p p₀ q q₀
  have left:=supported B D₁ true p₀
  have right:=supported B D₂ false q₀
  rw [B.bump.tsupport_eq] at left right
  have lower:=bottom left
  have upper:=bottom right
  change z 0 a ≤ chart a true p 0 a at lower
  change z 0 a ≤ chart a false q 0 a at upper
  rw [(time a p).2] at lower
  rw [(time a q).1] at upper
  have axial:=norm_le_pi_norm (p-q) a
  change |p a-q a| ≤ ‖p-q‖ at axial
  rw [dist_eq_norm]
  linarith only [neg_le_abs (p a-q a),axial,lower,upper]

theorem mass_at (D₁ D₂:ℕ)(p q:Point4):
    (profile B D₁ true).ψ.val p*(profile B D₂ false).ψ.val q=
      mass a x B (chart a true p,chart a false q):=by rw [value,value];rfl

end YM.Integration.WilsonIndependentConditionedGramBulbProfile
