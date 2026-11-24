import YM.MS.ScaleForest.Supports
/-!
# UV/IR and calibration, profiles

Final readout using the one convention; one can request even the test on
supported placements NOW, works on any such compact including in the
UV & ε stage (UV of each rank integration then test). Closes an IR cutoff
on all Laurent operands projected to these physical arms. Thus can apply
to the one explicit nonzero family we found for the Rose arms to say if
and where that family contributes to posted costs. This does NOT calculate
the *values* of all the rest on those profiles, but proves that this
actual forest prescription (incl. signs and subtractions) is WHAT to
integrate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Panels
open Function Filter Set MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Local.Physical
open Planted FVA2 FVA2.Position FVA2.Position.Axes FVA2.Arrival Dframe WilsonMS
open Normalize.Fray
open scoped Topology Classical BigOperators ENNReal
variable {G:Gauge} {n d:ℕ} (P:Palette G)(ν:ℝ)(V:Store G) (k:ℕ)
local notation "O"=> OpenAxis.Plot (Press.portDeck G)

variable (K:Set (Points n))(t:ℝ)

def onM (K:Set (Points n)): Rake.Position (Fin n) K:= fun i x=> Schedule.plot (x:Points n) i
lemma on_mesh (h:IsCompact K)(ht:K ⊆ conf n): MapGap (onM K):= by
    intro i j he; let f(x:Points n):= Schedule.plot x i-Schedule.plot x j; have hf:Continuous f:= by unfold f; exact ((continuous_apply i).comp Schedule.plot_exposes).sub ((continuous_apply j).comp Schedule.plot_exposes);
    rcases eq_empty_or_nonempty K with hK|hh
    · subst K; exact ⟨ hf.comp continuous_subtype_val,⟨ _,zero_lt_one,fun x=>x.property.elim⟩,⟨_,zero_lt_one,fun x=>x.property.elim⟩⟩
    have hu(x)(hx:x∈K):0< ‖f x‖:= norm_pos_iff.mpr (sub_ne_zero.mpr ((Schedule.track (ht hx)).ne he)); obtain ⟨a,ha,hA⟩:= h.exists_isMaxOn hh hf.norm.continuousOn; obtain ⟨b,hb,hB⟩:= h.exists_isMinOn hh hf.norm.continuousOn; exact ⟨ hf.comp continuous_subtype_val,⟨ _, hu a ha,fun i=>hA i.property⟩,⟨ _,hu b hb,fun i=> hB i.property⟩⟩

/-- These memorized prices are all exact formulae on compact geometry
with a specified common choice of basis and conversions. Using the same guards.
They don't introduce any calibration at the level of the **raw** amplitudes. -/
def capsule (Y: Fin n→ Toon G d)(k:ℕ)(s:ℝ) (z:ℂ)(x:↥K) := byPartition (staying P (inducted O ∘ flash ∘ Y) ν (onM K) s z x) Finset.univ k
def at_time (Y: Fin n→ Toon G d)(k:ℕ)(s:ℝ) (x:↥K):= byPartition (stayed P (inducted O ∘ flash ∘ Y) ν (onM K) s x) Finset.univ k
lemma still_gross (Y:Fin n → Toon G d)(h:IsCompact K)(hp:K ⊆ conf n):
    (∀ s, Stills dotty (capsule P ν K Y k s) (at_time P ν K Y k s)) ∧
    Stills atTop (at_time P ν K Y k) (K.restrict (gross P ν Y k)):= by
    let Gx:Fin n→ Script G:= inducted O ∘ flash ∘ Y; haveI:= isCompact_iff_compactSpace.mp h; have he A j:= Stills.eachNode ν _ (atlas_hired P Gx (onM K) (on_mesh K h hp) A j );
    constructor; · intro s; exact Stills.still_parts ( F:=fun z q=> staying P Gx ν (onM K) s z q ) (fun i k=> (he i k).1 s) _ _
    let M:= graph_data P (OpenAxis.Plot (Press.portDeck G)); rw [ show K.restrict (gross P ν Y k)=(fun (x:↥K)=> byPartition (priceMap P ν Gx (onM K) x) Finset.univ k) from ?_ ]; exact Stills.still_parts ( F:=fun z x=> stayed P Gx ν (onM K) z x ) (fun i k=> (he i k).2 ) _ _
    funext x; unfold Gx gross Set.restrict; dsimp only; rw [point_income P ν M (flash∘Y) (Schedule.track (hp x.property)), quoteVision P ν M (flash∘Y) (on_mesh K h hp), part_eq ]; rfl

def filmPoints (v:Tags G d n) (s:ℝ) (z:ℂ)(x:↥K) := ∑ a∈tally k n,∑ y:Fin n → Toon G d, capsule P ν K y (a none) s z x * each y (pulseU a (conversionG P ν V d) v)
def atPoints (v:Tags G d n)(s:ℝ)(x:↥K):=∑ a∈ tally k n,∑ y: Fin n → Toon G d, at_time P ν K y (a none) s x * each y (pulseU a (conversionG P ν V d) v)
lemma still_form (v:Tags G d n)(h:IsCompact K)(hp:K⊆ conf n):
    (∀ s, Stills dotty (filmPoints P ν V k K v s) (atPoints P ν V k K v s)) ∧
    Stills atTop (atPoints P ν V k K v) (fun x:↥K=> scaledResult P ν V d x.val k v) := by
    haveI:= isCompact_iff_compactSpace.mp h; constructor
    · intro s; unfold filmPoints atPoints; exact Stills.taleSum _ (fun a _=> Stills.taleSum _ (F:=fun y z x=> capsule P ν K y (a none) s z x *_) (fun y _=> Stills.mul (still_gross P ν (a none) K y h hp|>.1 s) (Stills.strokes continuous_const)))
    unfold atPoints; simp_rw [conversionFormula]; exact Stills.taleSum _ (fun a _=> Stills.taleSum _ (fun y _=> Stills.mul (still_gross P ν (a none) K y h hp|>.2) (Stills.strokes continuous_const)))

lemma providing (x:Points n)(hx:x∈conf n)(v:Tags G d n) :
    let K:Set (Points n):={x}; let i:↥K:= ⟨ x,rfl⟩;
    (∀ s,Tendsto (fun z=> filmPoints P ν V k K v s z i) dotty (𝓝 (atPoints P ν V k K v s i)))∧
    Tendsto (fun s=> atPoints P ν V k K v s i) atTop (𝓝 (scaledResult P ν V d x k v)) := by
    intro K i; obtain ⟨hP,h⟩:= still_form P ν V k K v (isCompact_singleton) (singleton_subset_iff.mpr hx); exact ⟨ fun s=>(hP s).stillPoint i,h.stillPoint i⟩

variable (p:Test n)
abbrev support := tsupport p
private lemma compact : IsCompact (support p):= p.hasCompactSupport
attribute [local instance] Measure.Subtype.measureSpace
noncomputable local instance : IsFiniteMeasure (MeasureTheory.volume:Measure ↥(support p)):= by constructor; change Measure.comap _ MeasureTheory.volume Set.univ<⊤; rw [comap_subtype_coe_apply (compact p).measurableSet ]; simpa using (compact p).measure_lt_top (μ:=MeasureTheory.volume)
local instance : CompactSpace ↥(support p):= isCompact_iff_compactSpace.mp (compact p)

/-- Extension to profiles. Actual layout chart uses its successive log lengths,
kept same through UV, ε, IR takes. Integrate with this supported measure. -/
def averaging (F: ↥(support p)→ℂ):= ∫ x:↥(support p),p (x:Points n) * F x
def landscape (v:Tags G d n)(s:ℝ)(z:ℂ):= averaging p (filmPoints P ν V k (support p) v s z)
def specialized (v:Tags G d n)(s:ℝ):= averaging p (atPoints P ν V k (support p) v s)
private lemma basis_integrable (x : C(↥(support p),ℂ)): Integrable (⇑x):= (map_continuous x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma warmth {F: C(↥(support p),ℂ)} : Integrable (fun i:↥(support p)=> p (i:Points n)*F i):= basis_integrable p ⟨ _,(p.continuous.comp continuous_subtype_val).mul (map_continuous F)⟩
lemma integral_cont : Continuous (fun i:C(↥(support p),ℂ)=> averaging p i):= by
    let L:C(↥(support p),ℂ) →ₗ[ℂ] ℂ:= {
      toFun:=fun i=> averaging p i
      map_add':= fun x y=> by unfold averaging; simp_rw [ContinuousMap.add_apply,mul_add]; exact integral_add (warmth p) (warmth p)
      map_smul':=fun c x=> by unfold averaging; simp_rw [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply,mul_left_comm (_:ℂ) c]; rw [ integral_const_mul] }
    let f(x:↥(support p)):= ‖p (x:Points n)‖; let C:=∫ x:↥(support p),f x; have hf:Integrable f:= ( p.continuous.norm.comp continuous_subtype_val ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); refine AddMonoidHomClass.continuous_of_bound L C ?_
    intro x; refine (norm_integral_le_of_norm_le (hf.mul_const ‖x‖) (Eventually.of_forall (fun i=>?_))).trans_eq (integral_mul_const ‖x‖ f)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm x i) (norm_nonneg _)
lemma still_covers {I:Type}{l:Filter I}{F:I→↥(support p)→ℂ}{f:↥(support p)→ℂ}(hf:Stills l F f): (∀ᶠ i in l, Integrable (fun x:↥(support p)=> p (x:Points n)* F i x)) ∧ Tendsto (fun i=> averaging p (F i)) l (𝓝 (averaging p f)):= by obtain ⟨A,a,h,rfl,hA⟩:= hf.certs; exact ⟨ h.mono (fun i hi=>by rw [hi]; exact warmth p ), (((integral_cont p).continuousAt (x:=a)).tendsto.comp hA).congr' (h.mono fun i hi=> congr_arg (averaging p) hi.symm) ⟩

theorem through_profile (v:Tags G d n) :
    (∀ s,Tendsto (landscape P ν V k p v s) dotty (𝓝 (specialized P ν V k p v s))) ∧ Tendsto (specialized P ν V k p v) atTop (𝓝 (priced P ν V d k n p v)):= by
    obtain ⟨hh,h⟩:=still_form P ν V k (support p) v (compact p) p.tsupport_subset
    obtain ⟨_,hu⟩:= still_covers p h
    refine ⟨fun s=> (still_covers p (hh s)).2, ?_⟩; rw [ show priced P ν V d k n p v=averaging p (fun x:↥(support p)=> scaledResult P ν V d x.val k v) from ?_ ]; exact hu
    rw [ reports_trace P ν V (graph_data P O), averaging, integral_subtype (compact p).measurableSet (fun x=> p x* scaledResult P ν V d x k v) ]; exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s:=support p) (fun i hi=> by rw [image_eq_zero_of_notMem_tsupport hi]; exact zero_mul _) ).symm
end YM.MS.ScaleForest.Panels
