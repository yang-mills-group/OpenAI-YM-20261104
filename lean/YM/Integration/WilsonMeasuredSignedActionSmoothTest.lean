import YM.Integration.WilsonMeasuredSignedActionSmoothPacket
import YM.Integration.WilsonMeasuredSignedActionEnrolled
/-! The oriented current, its signed unit face and one fixed smooth
reflected ordinary pair suffice on the actual limiting positive ray. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionSmoothTest
open Function Filter Set Spec Table Climb Trace Trace.Pilot PhysMS Maxwell Maxwell.Free
open Next.UVStress XSpace XSpace.Normalize XSpace.Stab Next.Rank OPE OPE.Orbits
open TopologicalSpace MeasureTheory PertExtension.Rigidity.Positive
open WilsonPhysicalPositionReflectedReturn (sites)
open WilsonMeasuredSignedActionSmoothPacket (reflected reading)
open WilsonMeasuredPublicEntranceCommonColor (carried)
open WilsonMeasuredPublicEntranceMarkedQuadratics (marked)
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G)
local notation "M" => Bel C.book
local notation "D₄" => (Bel C.book).Field 4

def singleton (w:D₄):ℂ:=expectation M 4 w
def Heard (b:ContDiffBump sites)(A:Module.End ℂ D₄):Prop:=
  singleton C (A (stepField C))=singleton C (stepField C) ∧
  reading C b (A (stepField C))=reading C b (stepField C)

theorem scale (b:ContDiffBump sites)(s:ℝ)(w:D₄):
    reading C b ((s:ℂ) • w)=(s:ℂ)^2 * reading C b w:=by
  let adj:=(Bel C.book).adj (spin_free C.labels) 4 0
  have same:adj ((s:ℂ) • w)=(s:ℂ) • adj w:=by
    rw [map_smulₛₗ]
    simp
  let pair:Fin 2→D₄:=![w,adj w]
  have two:(![(s:ℂ) • w,adj ((s:ℂ) • w)]:Fin 2→D₄)=fun i=>(s:ℂ) • pair i:=by
    funext i
    fin_cases i
    · rfl
    · exact same
  have bill(y:Points 2):reflected C ((s:ℂ) • w) y=(s:ℂ)^2 * reflected C w y:=by
    change (Bel C.book).classMoment M (fun _:Fin 2=>4) y ![(s:ℂ) • w,adj ((s:ℂ) • w)]=_
    have base:(Bel C.book).classMoment M (fun _:Fin 2=>4) y pair=reflected C w y:=rfl
    rw [two,←base]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
      ((Bel C.book).classMoment M (fun _:Fin 2=>4) y).map_smul_univ (fun _=>(s:ℂ)) pair
  unfold reading
  simp_rw [bill]
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  simp [Complex.real_smul,mul_left_comm]

theorem fixed (H:(Bel C.book).Hierarchy)(b:ContDiffBump sites)(alive:reading C b (stepField C)≠0)
    (A:Module.End ℂ D₄)(holds:Heard C b A)
    (ray:∃s:ℝ,0 ≤ s ∧ ∃a:ℂ,A (stepField C)=(s:ℂ) • stepField C+a • (Bel C.book).unit 4):
    A (stepField C)=stepField C ∧ carried C A (marked G (le_refl 4) 1)=marked G (le_refl 4) 1:=by
  obtain ⟨s,pos,c,land⟩:=ray
  have one:=holds.1
  unfold singleton at one
  rw [land,map_add,map_smul,map_smul,sceneV H,mean_unit H.laws,smul_zero,zero_add,smul_eq_mul,mul_one] at one
  rw [one,zero_smul,add_zero] at land
  have pair:=holds.2
  rw [land,scale] at pair
  have square:(s:ℂ)^2=1:=mul_right_cancel₀ alive (pair.trans (one_mul _).symm)
  have sq:s^2=1:=by exact_mod_cast square
  have exactScale:s=1:=by nlinarith
  have head:A (stepField C)=stepField C:=by simpa only [exactScale,Complex.ofReal_one,one_smul] using land
  refine ⟨head,?_⟩
  have moved:carried C A (fields C.labels 4 (stepField C))=fields C.labels 4 (stepField C):=by
    change fields C.labels 4 (A ((fields C.labels 4).symm (fields C.labels 4 (stepField C))))=_
    rw [LinearEquiv.symm_apply_apply,head]
  rw [←WilsonMeasuredSignedActionDirection.direct C,two_smul,map_add,moved]


theorem original (simple:G.Simple)(H:(Bel C.book).Hierarchy):
    ∃b:ContDiffBump sites,tsupport b⊆conf 2 ∧ ∀A:Module.End ℂ D₄,Heard C b A →
      (∃s:ℝ,0 ≤ s ∧ ∃u:ℂ,A (stepField C)=(s:ℂ) • stepField C+u • (Bel C.book).unit 4) →
      A (stepField C)=stepField C ∧ carried C A (marked G (le_refl 4) 1)=marked G (le_refl 4) 1:=by
  obtain ⟨b,placed,live⟩:=WilsonMeasuredSignedActionSmoothPacket.original C simple H
  exact ⟨b,placed,fun A cash ray=>fixed C H b live A cash ray⟩
end YM.Integration.WilsonMeasuredSignedActionSmoothTest
end
