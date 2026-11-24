import YM.Integration.WilsonOriginalTwoFlatRosePositions
import YM.Integration.WilsonNeutralOffsetCutoff

/-! Take all occupied Rose faces through the original physical position limit on one extraction.
Every cutoff arm, including its date-dependent lower coordinates, is held fixed across faces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseFaceLimits
open Function Filter Finset Set Metric Extraction Table Spec PhysMS
open MeasureTheory Lattice Wilson Source OPE.Orbits Cells Push.GridApprox
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourSquare
open WilsonPositionThermometerCapStation RG12 RG17 Trace.Pilot
open WilsonNeutralOffsetCutoff (named)
open WilsonPositionThermometerGradedSource (grade)
open scoped Topology Classical BigOperators

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(A:WilsonPositionThermometerCapStation.Group R.family 6)
    {Y:Ultrafilter (ℕ×ℕ)}
local notation "d" => fun i:Fin 3=>(grade i).val
local notation "E" => Finset (Fin 3)

def names (s:E):Fin (Fintype.card ↥s) ≃ ↥s:=(Fintype.equivFin s).symm

def loc (s:E)(x:Points 3):Points (Fintype.card ↥s):=points fun j=>x (names s j).val

theorem continuous_loc (s:E):Continuous (loc s):=by
  unfold loc points
  fun_prop

theorem separate (s:E){x:Points 3}(hx:x∈conf 3):loc s x∈conf (Fintype.card ↥s):=by
  intro i j eqn
  exact (names s).injective (Subtype.ext (hx eqn))

def raw (r:ℝ)(z:UVIndex)(x:Points 3)(s:E):ℂ:=
  let o:=wrap _ ∘ address (R.family.S.a z.1) (r • x)
  R.family.omega z.1 z.2 fun U=>∏i∈s,R.family.O z.1 z.2 (named R A z.1 z.2 i) (o i) U

def result (r:ℝ)(v:(i:Fin 3)→S.Field (d i))(x:Points 3)(s:E):ℂ:=
  S.classMoment S (fun j=>d (names s j).val) (r • loc s x) (fun j=>v (names s j).val)

include F in
theorem original (hG:G.Simple)(hl:(Y:Filter _)≤f.fuse)(r:ℝ)(rp:0<r)
    (v:(i:Fin 3)→S.Field (d i))
    (arms:(i:Fin 3)→Arm R.family S (Y:Filter _) (d i) (v i))
    (same:∀z i,(arms i).source z=named R A z.1 z.2 i)
    {K:Set (Points 3)}(compact:IsCompact K)(sep:K⊆conf 3){ε:ℝ}(ep:0<ε):
    ∀ᶠ z:UVIndex in (Y:Filter _),∀s:E,∀x∈K,dist (raw R A r z x s) (result R r v x s)<ε:=by
  apply Filter.eventually_all.mpr
  intro s
  let m:=Fintype.card (↥s)
  let e:=names s
  let heads:Caps m:=fun j=>d (e j).val
  let h(j:Fin m):=v (e j).val
  let arm(j:Fin m):Arm R.family S (Y:Filter _) (heads j) (h j):=arms (e j).val
  let near:=loc s '' K
  have kc:IsCompact near:=compact.image (continuous_loc s)
  have ks:near⊆conf m:=by rintro _ ⟨x,hx,rfl⟩;exact separate s (sep hx)
  filter_upwards [WilsonOriginalTwoFlatRosePositions.original F heads h arm hG hl r rp kc ks ep] with z seen x hx
  have atx:=seen (loc s x) ⟨x,hx,rfl⟩
  have id:raw R A r z x s=R.family.ensemble (N:=z.1) (p:=z.2) heads
      (wrap _ ∘ address (R.family.S.a z.1) (r • loc s x)) (fun j=>(arm j).source z):=by
    unfold raw
    change R.family.omega _ _ _=R.family.omega _ _ _
    congr 1;funext U
    let q(i:Fin 3):ℂ:=R.family.O z.1 z.2 (named R A z.1 z.2 i)
        (wrap _ (address (R.family.S.a z.1) (r • x) i)) U
    change ∏i∈s,q i=_
    rw [←Finset.prod_coe_sort s q]
    apply Fintype.prod_equiv e.symm
    intro i
    change q i.val=R.family.O _ _ ((arms (e (e.symm i)).val).source z) _ U
    rw [same,e.apply_symm_apply]
    dsimp only [q,Function.comp_apply,Extraction.address,loc,points]
    change R.family.O _ _ _ (wrap _ (fun a=>⌈(r • x) i.val a / R.family.S.a z.1⌉)) U =
      R.family.O _ _ _ (wrap _ (fun a=>⌈(r • x) (e (e.symm i)).val a / R.family.S.a z.1⌉)) U
    rw [e.apply_symm_apply]
    rfl
  rw [id]
  exact atx

end YM.Integration.WilsonOriginalTwoFlatRoseFaceLimits
end
