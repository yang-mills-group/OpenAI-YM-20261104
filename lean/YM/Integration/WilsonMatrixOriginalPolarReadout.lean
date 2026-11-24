import YM.Integration.WilsonInvariantActionIntegratedPair

/-! Ordered marginal and pair readings for arbitrary original representatives of grade four. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalPolarReadout
open Filter Function Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free Trace.Pilot
open TraceExtension Next.UVStress PhysicalNext.Repeat.Legato Lattice RG Wilson RGComparison.Core16
open Extraction Extraction.Order Push.GridApprox OPE OPE.Orbits OPE.Therm
open WilsonInvariantActionPairHistory hiding use
open WilsonInvariantActionPairCovariance WilsonInvariantActionPairMarginals
open WilsonInvariantActionIntegratedPair
open private tags use recorded from YM.Integration.WilsonInvariantActionIntegratedPair
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S)

include F in
theorem single_read (a : R.family.label 4) :
    f.limits (fun _=>True) (fun N p=> single R (a) (0:Site (R.family.side N p)))
      (expectation S 4 (S.project 4 a)) := by
  let v : Fin 1→R.family.book.Token:=fun _=>⟨4,a⟩
  let z : Points 1:=0
  let K : Set (Points 1):={z}
  have compact : IsCompact K:=isCompact_singleton
  have cyclic (p : ℕ) : K⊆Cyclic R.family.S p 1 := fun _ _ i j hij=>False.elim (hij (Subsingleton.elim i j))
  have generic : K⊆YM.generic 1 := fun _ _ _ _ _ _=>Subsingleton.elim ..
  obtain ⟨P,local_,outer⟩:=F.room.generic
  have grid0 (N : ℕ) : grid R.family N (fun _:Fin 1=>(0:Cover))=z := by
    ext i a
    simp [grid,points,Schedule.gridPoint,z]
  have native : S.read z v=expectation S 4 (S.project 4 a) := by
    rw [←S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl)
      (show z∈conf 1 from fun i j _=>Subsingleton.elim i j) v]
    have project : S.classTokens ∘ v=fun _:Fin 1=>(⟨4,S.project 4 a⟩:S.Tag) := by
      rfl
    rw [project,vev_coordinates F.room.kernel.translations]
    exact (onepoint S (S.project 4 a)).symm
  refine ⟨Eventually.of_forall fun _=>trivial,fun p=>(P p).read z v,fun p _=>?_,?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε he
    filter_upwards [local_.onK p 1 K compact (cyclic p) v ε he] with i hi
    have e:=hi (fun _:Fin 1=>(0:Cover)) ((grid0 _).symm ▸ (show z∈K from mem_singleton _))
    simpa [grid0,dist_eq_norm,WilsonInvariantActionPairMarginals.single,v] using e
  · rw [Metric.tendsto_nhds]
    intro ε he
    filter_upwards [outer 1 K compact generic v ε he] with i hi
    simpa [dist_eq_norm,native] using hi z (mem_singleton _)

include F in
theorem ordered (cut : (N p:ℕ)→Fin (N+1)) (φ : Test 2) {r : ℝ} (rp : 0<r) (first second : R.family.label 4) :
    f.limits (fun p=>suitable R.family.S p (dilate rp φ))
      (profile R cut first second (dilate rp φ))
      (WilsonInvariantActionPairCovariance.tested (S.project 4 first) (S.project 4 second) r φ) := by
  let id:=R.family.refUnit 4
  let t:=dilate rp φ
  let value (a:R.family.label 4) (x:Points 2):=S.read (r•x) (tags R a second)
  have raw (a:R.family.label 4) : f.limits (fun p=>suitable R.family.S p t)
      (fun N p=>smears R.family N p (tags R a second) t) (φ.applyTo (value a)) := by
    have reading:=F.room.ordered.reads 2 (tags R a second) (dilate rp φ)
    rw [zoom_integral] at reading
    exact reading
  have cash (a:R.family.label 4) : Integrable (fun x=>φ x*value a x) :=
    φ.smearing ((S.smooth_read F.room.kernel.smooth _).continuousOn.comp (by fun_prop) (fun _ hx=>Work.A05.smul_conf rp hx))
  have result : φ.applyTo (value first)-expectation S 4 (S.project 4 first)*φ.applyTo (value id)=
      WilsonInvariantActionPairCovariance.tested (S.project 4 first) (S.project 4 second) r φ := by
    unfold WilsonInvariantActionPairCovariance.tested Test.applyTo
    rw [←integral_const_mul,←integral_sub (cash first) ((cash id).const_mul _)]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx:x∈tsupport (φ:Points 2→ℂ)
    · have sep:=Work.A05.smul_conf rp (φ.tsupport_subset hx)
      dsimp only [value]
      rw [use F _ _ sep,use F _ _ sep,connected F _ _ sep,←placed]
      have one : S.project 4 id=S.unit 4:=rfl
      simp only [id,one,unit F (S.project 4 second) sep]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul,zero_mul,mul_zero,sub_zero]
  rw [←result]
  obtain ⟨existsP,fin,inner,outer⟩:=raw first
  obtain ⟨_,unitFin,unitInner,unitOuter⟩:=raw id
  obtain ⟨_,oneFin,oneInner,oneOuter⟩:=single_read F first
  refine ⟨existsP,fun p=>fin p-oneFin p*unitFin p,fun p hp=>?_,outer.sub (oneOuter.mul unitOuter)⟩
  apply ((inner p hp).sub ((oneInner p trivial).mul (unitInner p hp))).congr'
  filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop (R.family.ref 4))] with k hk
  exact (recorded R cut first second t hk).symm

end YM.Integration.WilsonMatrixOriginalPolarReadout
