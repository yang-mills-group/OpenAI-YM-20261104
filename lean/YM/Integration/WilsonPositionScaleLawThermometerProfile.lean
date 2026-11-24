import YM.Integration.WilsonPositionScaleLawThermometerChart

/-! The published ordinary rows are continuous jointly in the actual compact
ratio and the separated positions of the fixed original thermometer test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerProfile
open Function Filter Set Finset PowerSeries Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio)
open WilsonPositionScaleLawCompactIndependent (time continuousTime)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)[W:RangeSpec]

def row (t:Ratio)(x:Points 3):Badge→PowerSeries ℂ:=batchT (Jury.fxt (WilsonPositionScaleLawThermometerChart.response Z M ν (WilsonPositionScaleLawCompactIndependent.time t)) x)

include H in
omit W in
private theorem cash (j k:ℕ):Continuous (fun s=>coeff k (ψ Z M ν s^j)):=by
  induction j generalizing k with
  | zero=>simp only [pow_zero];exact continuous_const
  | succ j ih=>
    simp_rw [pow_succ,coeff_mul]
    apply continuous_finsetSum;intro i _
    exact (ih i.1).mul (continuous_iff_continuousAt.mpr fun s=>((H.details.normative ν).check.coupling s i.2).continuousAt)

include H in
theorem continuous (j:ℕ)(v:Badge):Continuous (fun z:Ratio×tsupport (Rose.test Z.criterion)=>coeff j (row Z M ν z.1 z.2.val v)):=by
  let φ:=Rose.test Z.criterion
  let U:=Measure.start Z.scheme Z.criterion 6
  let X:=Ratio×tsupport φ
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have hU:Jury.Thin U:=(Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base).light
  have point (k:ℕ):Continuous (fun z:X=>Jury.fxt U z.2.val k (Rose.missing (Rose.tag G) v)):=
    (hU 3 k (Rose.missing (Rose.tag G) v)).comp_continuous (continuous_subtype_val.comp continuous_snd) (fun z=>φ.tsupport_subset z.2.property)
  have w(k:ℕ):Continuous (fun z:X=>cut (ψ Z M ν (WilsonPositionScaleLawCompactIndependent.time z.1)) k j):=
    (cash Z M H ν k j).comp (continuousTime.comp continuous_fst)
  have same(z:X):coeff j (row Z M ν z.1 z.2.val v)=
      ∑k∈Iic j,cut (ψ Z M ν (WilsonPositionScaleLawCompactIndependent.time z.1)) k j*Jury.fxt U z.2.val k (Rose.missing (Rose.tag G) v):=by
    unfold row batchT WilsonPositionScaleLawThermometerChart.response;rw [coeff_mk,Jury.fxt_c,MS.Book.Program.rules]
    simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,U]
  exact (continuous_finsetSum _ (fun k _=>(w k).mul (point k))).congr (fun z=>(same z).symm)

include H in
theorem bound (q:ℕ):∃C:ℝ,0≤C ∧ ∀t:Ratio,∀x∈tsupport (Rose.test Z.criterion),∀v:Badge,∀k≤q,‖coeff k (row Z M ν t x v)‖≤C:=by
  let K:=tsupport (Rose.test Z.criterion)
  letI :CompactSpace K:=isCompact_iff_compactSpace.mp (Rose.test Z.criterion).hasCompactSupport
  let X:=Ratio×K
  have bnd(v:Badge)(k:Fin (q+1)):∃C:ℝ,0≤C ∧ ∀z:X,‖coeff k.val (row Z M ν z.1 z.2.val v)‖≤C:=by
    obtain ⟨C,hC⟩:BddAbove ((fun z:X=>‖coeff k.val (row Z M ν z.1 z.2.val v)‖) '' univ):=
      isCompact_univ.bddAbove_image (continuous Z M H ν k.val v).norm.continuousOn
    exact ⟨max C 0,le_max_right _ _,fun z=>(hC (mem_image_of_mem _ (mem_univ z))).trans (le_max_left _ _)⟩
  choose C hC h using bnd
  refine ⟨∑v,∑k,C v k,Finset.sum_nonneg (fun v _=>Finset.sum_nonneg (fun k _=>hC v k)),?_⟩
  intro t x hx v k hk
  let i:Fin (q+1):=⟨k,by omega⟩
  have inside:C v i≤∑j,C v j:=Finset.single_le_sum (fun j _=>hC v j) (Finset.mem_univ i)
  have outside:(∑j,C v j)≤∑a,∑j,C a j:=Finset.single_le_sum (fun a _=>Finset.sum_nonneg (fun j _=>hC a j)) (Finset.mem_univ v)
  exact (h v i (t,⟨x,hx⟩)).trans (inside.trans outside)

end YM.Integration.WilsonPositionScaleLawThermometerProfile
end
