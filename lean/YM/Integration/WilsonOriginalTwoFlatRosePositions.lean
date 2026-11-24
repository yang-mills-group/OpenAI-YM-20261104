import YM.Integration.WilsonMovingForkOpticalQuadrature
import YM.Integration.WilsonReflectedPublicAlignedPoints
import YM.Integration.WilsonPositionThermometerGradedReading

/-! The fine original Wilson lookup, including its actual cutoff-dependent
arm, converges uniformly on a separated support before the optical interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRosePositions
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox WilsonPositionThermometerReading
open WilsonThermometerUnitFilingFourSquare
open scoped Topology ContDiff Classical BigOperators

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
variable {Y:Ultrafilter (ℕ×ℕ)}{n:ℕ}(d:Caps n)(v:(i:Fin n) → S.Field (d i))
    (arms:(i:Fin n) → Arm R.family S (Y : Filter (ℕ×ℕ)) (d i) (v i))

include F in
theorem original (hG:G.Simple)(hl:(Y : Filter (ℕ×ℕ)) ≤ f.fuse)(r:ℝ)(hr:0<r)
    {K:Set (Points n)}(hk:IsCompact K)(sep:K⊆conf n){ε:ℝ}(he:0<ε):
    ∀ᶠ z:ℕ×ℕ in (Y : Filter (ℕ×ℕ)),∀ x∈K,
    dist (R.family.ensemble (N:=z.1) (p:=z.2) d (wrap _ ∘ address (R.family.S.a z.1) (r • x))
        (fun i=>(arms i).source z)) (S.classMoment S d (r • x) v)<ε:=by
  let vals(z:ℕ×ℕ):R.family.book.Vector d:=fun i=>(arms i).source z
  let a:R.family.book.Vector d:=fun i=>(arms i).label
  have measured(i):Tendsto (fun z=>vals z i) (Y : Filter (ℕ×ℕ)) (𝓝 (a i)):=(arms i).approaches
  have redraw(x:Points n)(hx:x∈K):S.classMoment S d (r • x) v=S.value d (r • x) a:=by
    have result:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) d (Work.A05.smul_conf hr (sep hx)) a
    have ids:(fun i=>S.project (d i) (a i))=v:=funext fun i=>(arms i).represents
    rwa [ids] at result
  let T := (fun x : Points n => r • x) '' K
  have compact : IsCompact T := hk.image (continuous_const_smul r)
  have apart : T ⊆ conf n := by rintro _ ⟨x,hx,rfl⟩;exact Work.A05.smul_conf hr (sep hx)
  obtain ⟨t,ht,inside⟩ := compact.exists_cthickening_subset_open (conf_open _) apart
  let U := cthickening t T
  have cu : IsCompact U := compact.cthickening
  let result (y : Points n) := S.value d y a
  have cont : ContinuousOn result U := ((F.room.kernel.smooth.on_conf d a).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (cu.uniformContinuousOn_of_continuous cont) (ε/2) (half_pos he)
  have atTop' : Tendsto (fun z : UVIndex => z.1) (Y : Filter _) atTop :=
    tendsto_atTop.mpr fun j => (large_mesh f j).filter_mono hl
  have fine : Tendsto (fun z : UVIndex => (4*n:ℝ)*R.family.S.a z.1) (Y : Filter _) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*n:ℝ))).mul (R.family.S.shrinks.comp atTop')
  have bank := WilsonMovingCalibratedFields.paid R hG F hl d vals a
    measured U cu inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z charged mesh x hx
  rw [redraw x hx]
  let X := r • x
  let c := address (R.family.S.a z.1) X
  let Y := tag (R.family.S.a z.1) c
  have inT : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (R.family.S.a_pos z.1) X).trans_lt mesh
  have inU : Y ∈ U := mem_cthickening_of_dist_le Y X t T inT (near.le.trans (min_le_left _ _))
  exact (dist_triangle _ (result Y) _).trans_lt
    (add_lt_add (charged c inU)
      (move Y inU X (self_subset_cthickening T inT) (near.trans_le (min_le_right _ _))) |>.trans_eq (add_halves ε))

end YM.Integration.WilsonOriginalTwoFlatRosePositions
end
