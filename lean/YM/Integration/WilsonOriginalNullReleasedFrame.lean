import YM.Integration.WilsonOriginalNullBareErased
import YM.Integration.WilsonCapturedPrimaryPointInverse

/-! Return the complete measured basis on the two actual vacuum carriers.
Solve in the lower measured coordinates before estimating either null source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedFrame
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay MeasureTheory
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonOriginalNullCorridor WilsonCapturedPrimaryPointInverse
open private oneStore from YM.Integration.WilsonOriginalNullBareRows
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){d N p s:ℕ}
local notation "C₀"=>R.family
local notation "Fr"=>R.family.labels.level d
local notation "Y"=>R.family.params
local notation "Sec"=>R.family.localSection d
local notation "side"=>R.family.side s p
local notation "κ"=>safety R.family s
local notation "P"=>R.family.path.rep N p s

def printed (W:Rep G side)(o:Site side)(h:Coefficient Fr side):(C₀).label d:=
  projection Fr Y W.p.threshold o h

def Released (live:s≤N)(home:Opened C₀ d s p)(W:Rep G side)(o:Site side)
    (h:Coefficient Fr side)(field:Config G side→ℂ)(rent:ℝ):Prop:=
  let x:=(fitting (C:=C₀) d N p s R.makes home live).symm (printed R W o h)
  ∃ z v:Coefficient Fr side,∃u e:ℝ,
    z.Format o Y W ∧ z.remBound o W κ u ∧ projection Fr Y W.p.threshold o z=0 ∧
    v.Format o Y P ∧ v.remBound o P κ e ∧ projection Fr Y (P).p.threshold o v=0 ∧
    u+e≤rent ∧
    calValues (C:=C₀) d N p s x ∘ translate o=field+z.density o Sec W+v.density o Sec P

theorem matrix (live:s≤N)(home:Opened C₀ d s p)(W:Rep G side)(o:Site side)
    (h:(Fr).Index→ Coefficient Fr side)(c:(C₀).label d) :
    let M:=fitting (C:=C₀) d N p s R.makes home live
    let D:=fun j=>printed R W o (h j)
    M (∑j,c j • M.symm (D j))=combine Fr D c:=by
  intro M D
  rw [map_sum]
  simp only [map_smul,LinearEquiv.apply_symm_apply]
  ext i
  simp [combine,Pi.smul_apply]

theorem original (live:s≤N)(home:Opened C₀ d s p)(W:Rep G side)(o:Site side)
    {a b r t k:ℝ}(law:W.Lawful a b r t k)(same:W.p=(P).p)
    (h:(Fr).Index→ Coefficient Fr side)(F:(Fr).Index→ Config G side→ℂ)(fee:(Fr).Index→ℝ)
    (earned:∀j,Released R live home W o (h j) (F j) (fee j))
    (v c:(C₀).label d)
    (matchMatrix:combine Fr (fun j=>printed R W o (h j)) c=fitting (C:=C₀) d N p s R.makes home live v) :
    ∃ z k:Coefficient Fr side,∃u e:ℝ,
      z.Format o Y W ∧ z.remBound o W κ u ∧ projection Fr Y W.p.threshold o z=0 ∧
      k.Format o Y P ∧ k.remBound o P κ e ∧ projection Fr Y (P).p.threshold o k=0 ∧
      u+e≤∑j,‖c j‖*fee j ∧
      calValues (C:=C₀) d N p s v ∘ translate o=(∑j,c j • F j)+z.density o Sec W+k.density o Sec P:=by
  classical
  let M:=fitting (C:=C₀) d N p s R.makes home live
  let D:=fun j=>printed R W o (h j)
  let x:=fun j=>M.symm (D j)
  have fill:(∑j,c j • x j)=v:=M.injective ((matrix R live home W o h c).trans matchMatrix)
  choose z k u e zf zp zn kf kp kn due value using earned
  have dims:=dimensions d N p s R.makes home.post live
  obtain ⟨z₀,zf₀,zp₀,zn₀,ze₀⟩:=oneStore R W o law (same ▸ dims.1) (same ▸ dims.2) c z u zf zp zn
  obtain ⟨k₀,kf₀,kp₀,kn₀,ke₀⟩:=oneStore R P o (R.makes.wilson.represents N p s live).good dims.1 dims.2 c k e kf kp kn
  refine ⟨z₀,k₀,_,_,zf₀,zp₀,zn₀,kf₀,kp₀,kn₀,?_,?_⟩
  · rw [←sum_add_distrib]
    apply sum_le_sum
    intro j _
    simpa only [mul_add] using mul_le_mul_of_nonneg_left (due j) (norm_nonneg (c j))
  · rw [←fill,ze₀,ke₀]
    let cm:=WilsonMatrixOriginalGermBasis.density C₀ R.makes d N p s home.post live
    funext U
    have lin:=congrFun (map_sum cm (fun j=>c j • x j) univ) (translate o U)
    change calValues (C:=C₀) d N p s (∑j,c j • x j) (translate o U)=_ at lin
    simp only [map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at lin
    simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Function.comp_apply,lin]
    rw [←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    have read:=congrFun (value j) U
    change calValues (C:=C₀) d N p s (x j) (translate o U)=_ at read
    change c j * calValues (C:=R.family) d N p s (x j) (Lattice.translate o U)=_
    rw [read]
    simp only [Pi.add_apply]
    ring

end YM.Integration.WilsonOriginalNullReleasedFrame
