import YM.Integration.WilsonPositionProgramTrialPublicJointFourShell

/-! With three simple-gauge energy insertions, lower-horizon surveys on the same
finite tree carry only the common constant. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourHorizons
open Finset Labels XSpace XSpace.Cirrus XSpace.Rose XSpace.Normalize
open PhysicalNext.Repeat.Legato
open WilsonOriginalPublicFigureWick (superior)
open scoped Classical BigOperators
variable {G:Gauge}{h l n:ℕ}
theorem scalar (F:Frame G l)(simple:G.Simple)(low:l<4)(p:Label G l):
    ∃s:ℂ,p=s • unit G l:=by
  have only (i:F.Index):i=0:=by
    by_contra diff
    have pos:=F.factors_pos i diff
    have notOne:=WilsonMaxwellThermometerWardColors.arity simple F i
    have slots:=WilsonMaxwellThermometerChargedHeads.graded F i
    have bound:=F.bound i
    omega
  refine ⟨F.basis.repr p 0,?_⟩
  calc
    p=∑i,F.basis.repr p i • F.basis i:=(F.basis.sum_repr p).symm
    _=F.basis.repr p 0 • F.basis 0:=sum_eq_single_of_mem 0 (mem_univ _) fun i _ ne=>(ne (only i)).elim
    _=_:=by rw [F.starts_unit]

theorem same (R:Run G)(W:Initialize G)(simple:G.Simple)(cap:h≤4)(le:l≤h)
    (Z:Sample n)(o:Z.F.Sites)(v:On.Grade G l):
    Bare.column (W.tree Z.F.p) (W.surveys h) o (On.sectionMap h (en le v))=
      On.stencil W.hol (W.surveys l) Z.F.p (W.tree Z.F.p) o v:=by
  by_cases top:l=h
  · subst h;rfl
  let p:Sec G l:=⟨v.val,v.property.1⟩
  have raised:On.sectionMap h (en le v)=raiseLabel G le (On.sectionMap l p):=(On.raised le p).symm
  change Bare.column _ _ _ _=Bare.column _ _ _ (On.sectionMap _ p)
  obtain ⟨s,eq⟩:=scalar (R.family.labels.level l) simple (by omega) (On.sectionMap l p)
  have unit_:raiseLabel G le (unit G l)=unit G h:=rfl
  rw [raised,eq,map_smul,map_smul,map_smul,unit_,Bare.column_unit,Bare.column_unit]

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(cap:h≤4)(Z:Sample n)(o:Z.F.Sites)
    (a:(R.family.labels.level h).Coeff):superior W (R.family.labels.level h) Z o a=0:=by
  unfold superior
  apply sum_eq_zero
  intro k _
  exact sub_eq_zero.mpr (same R W simple cap _ Z o _)

end YM.Integration.WilsonPositionProgramTrialPublicJointFourHorizons
