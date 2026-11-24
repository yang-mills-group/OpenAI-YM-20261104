import YM.Integration.WilsonSeparatedOriginalSlabPhysicalBlade
import YM.Integration.WilsonSeparatedOriginalSlabMaskPhases

/-! Finite superposition of the actual useful marked fields, including their regular and forced rows at a single genuine anchor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabBladeModule
open Function Finset MeasureTheory Lattice Wilson RG Source Push Local MergeProof Accent Marker
open RG05Readout RG05Readout.Address RG05Readout.View Extra.Trajectories
open WilsonReportHarvestSlabLabels WilsonReportHarvestSlabShiftLabels
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}(Y:RG.Rep G n)(o:Site n)

def Filed (f:Goods G n)(a:ℝ):Prop:=∃x:Three G n,Useful Y x ∧ x.1=f ∧
    MergeProof.Float.Blade Y o x.2.1 (profile Y.activities x.2.2) 0 a

theorem scale {f:Goods G n}{a:ℝ}(h:Filed Y o f a)(v:ℂ):Filed Y o (v • f) (‖v‖*a):=by
  obtain ⟨x,use,read,paid⟩:=h
  refine ⟨v • x,Useful.smul Y x v use,congrArg (v • ·) read,?_⟩
  change MergeProof.Float.Blade _ _ (v • x.2.1) (profile _ (v • x.2.2)) 0 _
  rw [profile_scale];simpa only [mul_zero] using paid.rate v

theorem add {σ C Λ δ w:ℝ}(law:Y.Lawful σ C Λ δ w){f g:Goods G n}{a b:ℝ}
    (F:Filed Y o f a)(H:Filed Y o g b):Filed Y o (f+g) (a+b):=by
  obtain ⟨x,hx,ex,dx⟩:=F;obtain ⟨y,hy,ey,dy⟩:=H
  refine ⟨x+y,Useful.join Y law hx hy,congr_arg₂ (·+·) ex ey,?_⟩
  change MergeProof.Float.Blade _ _ (x.2.1+y.2.1) (profile _ (x.2.2+y.2.2)) 0 _
  rw [MergeProof.Float.prof_add _ hx.normK hy.normK];simpa only [add_zero] using dx.comp dy

theorem finite {σ C Λ δ w:ℝ}(law:Y.Lawful σ C Λ δ w){ι:Type*}[Nonempty ι]
    (f:ι → Goods G n)(a:ι → ℝ)(all:∀i,Filed Y o (f i) (a i))(t:Finset ι):
    Filed Y o (∑i∈t,f i) (∑i∈t,a i):=by
  classical
  induction t using Finset.induction_on with
  | empty=>simpa using scale Y o (all (Classical.choice ‹Nonempty ι›)) 0
  | insert i t hi ih=>simpa only [Finset.sum_insert hi] using add Y o law (all i) ih

theorem mask {σ C Λ δ w:ℝ}(law:Y.Lawful σ C Λ δ w)(F:Config G n → Poly (Stock.census (Fin 3)))
    {a:ℝ} (h:∀b:Fin 8,Filed Y o (fun W=>(translated (WilsonSeparatedOriginalSlabMaskPhases.shift b) (F W)).part entire) a)
    (q:(Stock.census (Fin 3)).Mode):Filed Y o (fun W=>(F W).part q) a:=by
  let t:=WilsonSeparatedOriginalSlabMaskPhases.weight q
  let v:=WilsonSeparatedOriginalSlabMaskPhases.shift
  let R:Fin 8 → Goods G n:=fun b W=>(translated (v b) (F W)).part entire
  have paid:=finite Y o law (fun b:Fin 8=>t b • R b) (fun b:Fin 8=>‖t b‖*a)
    (fun b=>scale Y o (h b) (t b)) Finset.univ
  have eq:(∑b:Fin 8,t b • R b)=(fun W=>(F W).part q):=by
    funext W;simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using WilsonSeparatedOriginalSlabMaskPhases.original (F W) q
  rwa [eq,←Finset.sum_mul,WilsonSeparatedOriginalSlabMaskPhases.price,one_mul] at paid

end YM.Integration.WilsonSeparatedOriginalSlabBladeModule
