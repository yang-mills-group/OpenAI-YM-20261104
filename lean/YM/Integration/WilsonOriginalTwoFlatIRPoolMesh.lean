import YM.Integration.WilsonOriginalTwoFlatIRSocketProper
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolMesh
open Function Filter Finset Set Metric Extraction Table Spec PhysMS
open MeasureTheory Lattice Wilson Source OPE.Orbits Cells Push.GridApprox
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourSquare
open WilsonPositionThermometerCapStation RG12 RG17 Trace.Pilot
open WilsonNeutralOffsetCutoff (named)
open WilsonPositionThermometerGradedSource (grade)
open scoped Topology Classical BigOperators

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)
    {Y:Ultrafilter (ℕ×ℕ)}
local notation "d" => fun i:Fin 3=>(grade i).val
local notation "E" => Finset (Fin 3)

open WilsonOriginalTwoFlatRoseFaceLimits (names loc result continuous_loc separate)
def raw (r:ℝ)(p:UVIndex)(Y:(i:Fin 3)→R.family.label (d i))(x:Points 3)(s:E):ℂ :=
  R.family.omega p.1 p.2 (WilsonOriginalTwoFlatRoseSecant.field R Y
    (wrap _ ∘ address (R.family.S.a p.1) (r • x)) s)

include F in
theorem limit (hG:G.Simple)(hl:(Y:Filter _)≤f.fuse)(r:ℝ)(rp:0<r)
    (v:(i:Fin 3)→S.Field (d i))
    (arms:(i:Fin 3)→Arm R.family S (Y:Filter _) (d i) (v i))
    {K:Set (Points 3)}(compact:IsCompact K)(sep:K⊆conf 3){ε:ℝ}(ep:0<ε):
    ∀ᶠ z:UVIndex in (Y:Filter _),∀s:E,∀x∈K,dist (raw R r z (fun i=>(arms i).source z) x s) (result R r v x s)<ε:=by
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
  have id:raw R r z (fun i=>(arms i).source z) x s=R.family.ensemble (N:=z.1) (p:=z.2) heads
      (wrap _ ∘ address (R.family.S.a z.1) (r • loc s x)) (fun j=>(arm j).source z):=by
    unfold raw WilsonOriginalTwoFlatRoseSecant.field
    change R.family.omega _ _ _=R.family.omega _ _ _
    congr 1;funext U
    let q(i:Fin 3):ℂ:=R.family.O z.1 z.2 ((arms i).source z)
        (wrap _ (address (R.family.S.a z.1) (r • x) i)) U
    change ∏i∈s,q i=_
    rw [←Finset.prod_coe_sort s q]
    apply Fintype.prod_equiv e.symm
    intro i
    change q i.val=R.family.O _ _ ((arms (e (e.symm i)).val).source z) _ U
    rw [e.apply_symm_apply]
    dsimp only [q,Function.comp_apply,Extraction.address,loc,points]
    change R.family.O _ _ _ (wrap _ (fun a=>⌈(r • x) i.val a / R.family.S.a z.1⌉)) U =
      R.family.O _ _ _ (wrap _ (fun a=>⌈(r • x) (e (e.symm i)).val a / R.family.S.a z.1⌉)) U
    rw [e.apply_symm_apply]
  rw [id]
  exact atx

local notation "C" => R.family
theorem pointsAt (φ:Test 3){r τ:ℝ}(rp:0<r){f N per:ℕ}(live:f≤N)
    (mesh:4*(3:ℝ)*(C).S.a f≤τ*r)(cell:WilsonReceivedChronologicalFixedRoseVariation.cells R φ r (f,per)):
    ∃x∈cthickening τ (tsupport (φ:Points 3→ℂ)),∀i:Fin 3,
      wrap ((C).side N per) (address ((C).S.a N) (r • x) i)=((C).S.toDepth live per).embed (cell.val i):=by
  obtain ⟨x,placed,hit⟩:=WilsonSeparatedPrefixCellProfile.active φ ((C).S.a f) r ((C).side f per)
    ((C).S.a_pos f) cell.val (WilsonReceivedChronologicalFixedRoseVariation.charged R φ r (f,per) cell)
  let o:=address ((C).S.a f) (r • x)
  let y:=r⁻¹ • tag ((C).S.a f) o
  have actual:r • y=tag ((C).S.a f) o:=by simp [y,smul_smul,rp.ne']
  have err:=Extraction.approximate ((C).S.a_pos f) (r • x)
  have scale:dist (tag ((C).S.a f) o) (r • x)=r*dist y x:=by
    rw [←actual,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos rp,dist_eq_norm]
  have near:dist y x≤τ:=(mul_le_mul_iff_right₀ rp).mp (by rw [←scale];exact err.trans (mesh.trans_eq (mul_comm _ _)))
  refine ⟨y,mem_cthickening_of_dist_le y x τ _ (subset_tsupport _ hit) near,?_⟩
  intro i
  have atF:wrap ((C).side f per) (o i)=cell.val i:=congrFun placed i
  rw [actual,←atF]
  exact WilsonReflectedPublicAlignedPoints.grid R live per o i

end YM.Integration.WilsonOriginalTwoFlatIRPoolMesh
end
