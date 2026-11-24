import YM.Integration.WilsonOriginalCensusChildPages
import YM.Integration.WilsonOriginalCensusOrbitCenters
import YM.Integration.WilsonNeutralTwoPrintPathInheritedPeriod

/-! An actual choice of one fine page for each occupied inherited print
determines its own parent page and retains its original child digit. The
wrapped affine input on this coarse layout is the actual selected fine lift. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathFineFiber
open Function Finset Lattice RG Wilson
open WilsonCoeffUV.Winding WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos WilsonCoeffUV.Power WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonPointChildRelativeLift (centers)
open WilsonOriginalRelativePageTail (retained chosen)
open WilsonOriginalCensusOrbitCenters (layout)
open scoped Classical BigOperators
variable {I:Type}[DecidableEq I]{n f X F:Side}
variable (P:Patch)(u:f.val=n.val*P.L.val)(v:F.val=X.val*P.L.val)(h:n.val∣X.val)(H:f.val∣F.val)
  (S:Finset I)(address:I→Site f)(p:S→Fin (Pages f F))

def fine (i:I):Cover:=if hi:i∈S then lift (page H (address i) (p ⟨i,hi⟩)).val else 0

def parent (i:S):Site X:=(Ratio.mk P.L v:Ratio X F).parent (page H (address i.val) (p i)).val

def seats (o:S):I → Cover:=
  let sites:((S.erase o.val)→Site X):=fun i=>parent P v H S address p ⟨i.val,Finset.mem_of_mem_erase i.prop⟩
  layout h S o.val (parent P v H S address p o) sites (retained h sites)

omit [DecidableEq I] in
theorem numbered (i:S):
    parent P v H S address p i=(page h ((Ratio.mk P.L u:Ratio n f).parent (address i.val))
      ((WilsonOriginalCensusChildPages.choice u v h H (address i.val)).symm (p i))).val:=by
  let eqv:=WilsonOriginalCensusChildPages.choice u v h H (address i.val)
  have chosen:=WilsonOriginalCensusChildPages.parent u v h H (address i.val) (eqv.symm (p i))
  change (Ratio.mk P.L v:Ratio X F).parent (page H (address i.val) (eqv (eqv.symm (p i)))).val=_ at chosen
  simpa only [Equiv.apply_symm_apply,parent,eqv] using chosen

include h in
omit [DecidableEq I] in
theorem assembled (i:S):
    (Ratio.mk P.L v:Ratio X F).assemble (parent P v H S address p i,
      (Ratio.mk P.L u:Ratio n f).residue (address i.val))=(page H (address i.val) (p i)).val:=by
  let eqv:=WilsonOriginalCensusChildPages.choice u v h H (address i.val)
  have actual:=WilsonOriginalCensusChildPages.located u v h H (address i.val) (eqv.symm (p i))
  change (page H (address i.val) (eqv (eqv.symm (p i)))).val=_ at actual
  rw [numbered P u v h H S address p i]
  simpa only [Equiv.apply_symm_apply,eqv] using actual.symm

omit u in
theorem rooted (o i:S):wrap X (seats P v h H S address p o i.val)=parent P v H S address p i:=by
  by_cases same:i.val=o.val
  · obtain rfl:=Subtype.ext same
    simp [seats,layout,toe]
  · have hit:i.val∈S.erase o.val:=Finset.mem_erase.mpr ⟨same,i.prop⟩
    simp [seats,layout,toe,same,hit,centers,chosen,map_add,wrap_lift]

theorem original (o i:S):
    wrap F (chartIn P (seats P v h H S address p o) (fun j=>(Ratio.mk P.L u:Ratio n f).residue (address j)) i.val)=
      wrap F (fine H S address p i.val):=by
  change wrap F (P.L.val • seats P v h H S address p o i.val+
    lift ((Ratio.mk P.L u:Ratio n f).residue (address i.val)))=_
  rw [map_add,←(Ratio.mk P.L v:Ratio X F).embed_wrap,rooted P v h H S address p o i]
  have field:=assembled P u v h H S address p i
  unfold Ratio.assemble at field
  rw [field]
  simp [fine,i.prop]

end YM.Integration.WilsonNeutralTwoPrintPathFineFiber
end
