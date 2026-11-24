import YM.WilsonCoeffUV.Product.Report.UVLimit
import YM.Integration.WilsonMaxwellThermometerReflectedIncidence

/-! The two independently placed reflected compact probes, as the actual
separated inputs to the normalized two-cutoff programme. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramReflectedPurse
open Function Set Filter MeasureTheory WithLp Table.Pairing Lattice Wilson WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider WilsonMaxwellThermometerReflectedIncidence
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}

private def singlePoint : E4 ≃ₗ[ℝ] Points 1 where
  toFun:=site
  invFun y:=y 0
  left_inv _:=rfl
  right_inv y:=by apply PiLp.ext; intro i; fin_cases i; rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private def oneSite : E4 ≃L[ℝ] Points 1 where
  toLinearEquiv:=singlePoint
  continuous_toFun:= (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 1=>E4)).symm.continuous.comp
    (continuous_pi fun _=>continuous_id)
  continuous_invFun:= (continuous_apply (0:Fin 1)).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 1=>E4)).continuous

private def domain (a:Axis) (i:Fin 2):E ≃L[ℝ] Points 1:=
  let e: E ≃L[ℝ] E4 := (PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).symm
  let transform: E4 ≃L[ℝ] E4:=if i=0 then (Signed.reflect a).motion.toContinuousLinearEquiv
    else ContinuousLinearEquiv.refl ℝ _
  (e.trans transform).trans oneSite

def shape (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a)(i:Fin 2):E → ℝ :=
  B.r ∘ domain a i

private lemma real_support (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a):
    tsupport B.r=tsupport B.f:=by
  unfold tsupport Table.Pairing.Bulb.f
  congr 1
  ext z
  simp [Function.mem_support]

private lemma ticket (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a)(i:Fin 2)(d:ℕ):
    ∃φ:Rarity d,φ.ψ.val=shape a x B i:=by
  have smooth:ContDiff ℝ ∞ (shape a x B i):=B.bump.contDiff_normed.comp (domain a i).contDiff
  have compact:IsCompact (tsupport B.r):=by rw [real_support, B.controls]; exact isCompact_closedBall ..
  have support:HasCompactSupport (shape a x B i):=by
    change IsCompact (tsupport (B.r ∘ (domain a i).toHomeomorph))
    rw [tsupport_comp_eq_preimage]
    exact (domain a i).toHomeomorph.isCompact_preimage.mpr compact
  have admissible:shape a x B i ∈ Molli d := by
    change ContDiff ℝ (↑d) (shape a x B i)
    exact contDiff_infty.mp smooth d
  obtain ⟨φ,filed⟩:=scenery (⟨shape a x B i,admissible⟩:Phrase d) support
  exact ⟨φ,congrArg Subtype.val filed⟩

private lemma separate (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a):
    Disjoint (tsupport (shape a x B 0)) (tsupport (shape a x B 1)) := by
  apply Set.disjoint_left.mpr
  intro q h₀ h₁
  have found (i:Fin 2)(h:q∈tsupport (shape a x B i)):0<(domain a i q) 0 a:=by
    change q∈tsupport (B.r ∘ (domain a i).toHomeomorph) at h
    rw [tsupport_comp_eq_preimage] at h
    have live : domain a i q ∈ tsupport B.f := real_support a x B ▸ h
    exact (B.controlled _ live).2 0
  have left:=found 0 h₀
  have right:=found 1 h₁
  change 0 < (if (0:Fin 2)=0 then (Signed.reflect a).motion.toContinuousLinearEquiv
    else ContinuousLinearEquiv.refl ℝ _) (toLp 2 q) a at left
  change 0 < (if (1:Fin 2)=0 then (Signed.reflect a).motion.toContinuousLinearEquiv
    else ContinuousLinearEquiv.refl ℝ _) (toLp 2 q) a at right
  simp at left right
  linarith

theorem original (Q:Fin 2→SealR G)(a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a)(y:ℝ):
    ∃φ:Wilt Q, (∀i,(φ i).ψ.val=shape a x B i) ∧
      ∃fees:Fin 2→ℝ, ∀ᶠ Z:ℝ in atTop,Bough Q φ y Z fees := by
  choose φ eq using fun i:Fin 2=>ticket a x B i (Q i).D
  refine ⟨φ,eq,adequateZ Q φ ?_ y⟩
  intro i j neq
  simp only [eq]
  fin_cases i <;> fin_cases j
  · exact (neq rfl).elim
  · exact separate a x B
  · exact (separate a x B).symm
  · exact (neq rfl).elim

end YM.Integration.WilsonPositionProgramReflectedPurse
end
