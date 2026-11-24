import YM.Integration.WilsonInvariantActionAdmittedPair

/-! The deposited Ward field and the previously selected exterior may both move
inside the original signed Wilson cutoff covariance, with both finite-vacuum means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionDoubleAdmission
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Climb Table Spec PhysMS
open Lattice Wilson RG RG17 Extraction Extraction.Order Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato Pier.Lair SharpGram.Lenses FVA2 FVA2.Register
open Trace.Pilot TraceExtension OPE OPE.Orbits OPE.Therm
open WilsonInvariantActionIntegratedPair WilsonInvariantActionPairMarginals
open WilsonPositionHomogeneousFrame WilsonInvariantActionSpectatorPrices
open private tags recorded use from YM.Integration.WilsonInvariantActionIntegratedPair
open private pair smear from YM.Integration.WilsonInvariantActionAdmittedPair
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (L : Layout F) {U : Filter (ℕ×ℕ)} [U.NeBot] (chosen : U≤L.lens)

include F in
private theorem upper (a : R.family.label 4) : f.limits (fun _=>True)
    (fun N p=>single R a (0:Site (R.family.side N p))) (expectation S 4 (S.project 4 a)) := by
  let v : Fin 1→R.family.book.Token:=fun _=>⟨4,a⟩
  let z : Points 1:=0
  let K : Set (Points 1):={z}
  have compact : IsCompact K:=isCompact_singleton
  have cyclic (p : ℕ) : K⊆Cyclic R.family.S p 1:=fun _ _ i j hij=>False.elim (hij (Subsingleton.elim i j))
  have generic : K⊆YM.generic 1:=fun _ _ _ _ _ _=>Subsingleton.elim ..
  obtain ⟨T,local_,outer⟩:=F.room.generic
  have grid0 (N : ℕ) : grid R.family N (fun _:Fin 1=>(0:Cover))=z := by
    ext i coord
    simp [grid,points,Schedule.gridPoint,z]
  have value : S.read z v=expectation S 4 (S.project 4 a) := by
    rw [←S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl)
      (show z∈conf 1 from fun i j _=>Subsingleton.elim i j) v]
    change S.useAt S z (fun _ : Fin 1=>(⟨4,S.project 4 a⟩:S.Tag))=_
    rw [vev_coordinates F.room.kernel.translations]
    exact (onepoint S (S.project 4 a)).symm
  refine ⟨Eventually.of_forall fun _=>trivial,fun p=>(T p).read z v,fun p _=>?_,?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε he
    filter_upwards [local_.onK p 1 K compact (cyclic p) v ε he] with i hi
    have e:=hi (fun _:Fin 1=>(0:Cover)) ((grid0 _).symm ▸ (show z∈K from mem_singleton _))
    simpa [grid0,dist_eq_norm,WilsonInvariantActionPairMarginals.single,v] using e
  · rw [Metric.tendsto_nhds]
    intro ε he
    filter_upwards [outer 1 K compact generic v ε he] with i hi
    simpa [dist_eq_norm,value] using hi z (mem_singleton _)

include F chosen in
private theorem mean {r : ℝ} (live : R.family.ref 4≤L.level r) (a : R.family.label 4) :
    Tendsto (fun z:ℕ×ℕ=>single R (atRef L 4 r z a) (0:Site (R.family.side z.1 z.2))) U
      (𝓝 (expectation S 4 (master L 4 r a))) := by
  let E : Fin 1→Type:=fun _=>R.family.label 4
  let M (z : ℕ×ℕ) := R.family.ensemble (N:=z.1) (p:=z.2) (fun _:Fin 1=>4) (fun _=>0)
  let val (x : ∀i,E i) := expectation S 4 (S.project 4 (x 0))
  have all_ (x : ∀i,E i) : Tendsto (fun z:ℕ×ℕ=>M z x) U (𝓝 (val x)) := by
    have one : (fun _ : Fin 1=>x 0)=x := funext fun i=>congr_arg x (Subsingleton.elim _ _)
    have limit:=(along (upper F (x 0))).mono_left (chosen.trans L.certified)
    change Tendsto (fun z:ℕ×ℕ=>M z (fun _=>x 0)) U (𝓝 (val x)) at limit
    rwa [one] at limit
  let value : ∀i,E i:=fun _=>locatedRef L 4 r a
  let measured (z : ℕ×ℕ) : ∀i,E i:=fun _=>atRef L 4 r z a
  have result:=tendsto_multi (ι:=Fin 1) E M val all_ value measured
    (fun _=>tendsRef (L:=L) (D:=4) (r:=r) (v:=fun _=>a) chosen tendsto_const_nhds live)
  change Tendsto _ U (𝓝 (expectation S 4 (S.project 4 (locatedRef L 4 r a)))) at result
  rwa [payRef] at result

include F chosen in
private theorem pairSmear {r : ℝ} (live : R.family.ref 4≤L.level r) (a b : R.family.label 4)
    (φ : Test 2) :
    let fixedA:=S.representative 4 (master L 4 r a)
    let fixedB:=S.representative 4 (master L 4 r b)
    Tendsto (fun z:ℕ×ℕ=>smears R.family z.1 z.2 (tags R (atRef L 4 r z a) (atRef L 4 r z b)) φ-
      smears R.family z.1 z.2 (tags R fixedA fixedB) φ) U (𝓝 0) := by
  intro fixedA fixedB
  let raw:=fun w:R.family.label 4=>locatedRef L 4 r w
  have each (i : Fin 2) :
      Tendsto (fun z:ℕ×ℕ=>pair (atRef L 4 r z a) (atRef L 4 r z b) i) U (𝓝 (pair (raw a) (raw b) i)) := by
    fin_cases i <;> exact tendsRef (L:=L) (D:=4) (r:=r) chosen tendsto_const_nhds live
  have m:=calibrated_smear (v:=fun z=>pair (atRef L 4 r z a) (atRef L 4 r z b)) (x:=pair (raw a) (raw b))
    F.room.ordered U (chosen.trans L.certified) φ each
  have s:=calibrated_smear (v:=fun _=>pair fixedA fixedB) (x:=pair fixedA fixedB)
    F.room.ordered U (chosen.trans L.certified) φ (fun _=>tendsto_const_nhds)
  have eq : S.integralOn (fun _:Fin 2=>4) (pair (raw a) (raw b)) φ=S.integralOn (fun _:Fin 2=>4) (pair fixedA fixedB) φ := by
    apply φ.apply_eq
    intro x hx
    change S.read x (tags R (raw a) (raw b))=S.read x (tags R fixedA fixedB)
    rw [use F _ _ hx,use F _ _ hx,show S.project 4 (raw a)=S.project 4 fixedA from (payRef L a).trans (S.rep 4 _).symm,
      show S.project 4 (raw b)=S.project 4 fixedB from (payRef L b).trans (S.rep 4 _).symm]
  simpa only [eq,sub_self] using! m.sub s

include F chosen in
theorem measured {r : ℝ} (live : R.family.ref 4≤L.level r) (a b : R.family.label 4) (φ : Test 2)
    (cut : (N p:ℕ)→Fin (N+1)) :
    let fixedA:=S.representative 4 (master L 4 r a)
    let fixedB:=S.representative 4 (master L 4 r b)
    Tendsto (fun z:ℕ×ℕ=>profile R cut (atRef L 4 r z a) (atRef L 4 r z b) φ z.1 z.2-
      profile R cut fixedA fixedB φ z.1 z.2) U (𝓝 0) := by
  intro fixedA fixedB
  have covered:=chosen.trans L.certified
  let unit:=R.family.refUnit 4
  let I:=S.integralOn (fun _:Fin 2=>4) (pair unit fixedB) φ
  have identical : Tendsto (fun z:ℕ×ℕ=>smears R.family z.1 z.2 (tags R unit fixedB) φ) U (𝓝 I) :=
    (along (F.room.ordered.reads 2 (tags R unit fixedB) φ)).mono_left covered
  have drifting : Tendsto (fun z:ℕ×ℕ=>smears R.family z.1 z.2 (tags R unit (atRef L 4 r z b)) φ) U (𝓝 I) := by
    simpa only [fixedB,sub_add_cancel,zero_add] using! (smear F L chosen live unit b φ).add identical
  have first:=(along (converge F (master L 4 r a))).mono_left covered
  have diff:=(pairSmear F L chosen live a b φ).sub (((mean F L chosen live a).mul drifting).sub (first.mul identical))
  have raw:=diff.congr' (f₂:=fun z:ℕ×ℕ=>profile R cut (atRef L 4 r z a) (atRef L 4 r z b) φ z.1 z.2-
    profile R cut fixedA fixedB φ z.1 z.2) (by
    filter_upwards [((Cards.largeMesh f).eventually_ge_atTop (R.family.ref 4)).filter_mono covered] with z hz
    rw [recorded R cut _ _ φ hz,recorded R cut fixedA fixedB φ hz]
    ring)
  simpa only [sub_self] using! raw

variable (J : ℝ→tower S) {H : (Bel R.family.book).Hierarchy} (lead : Leading F J)
    (paid : ∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    {u : Filter (ℕ×ℕ)} (B : Mantle F u) (E : Services R.family f S) (pegs : Pegs B L)
    (near : ∀ᶠr in trail,R.family.S.a (L.level r)≤r ∧
      r≤R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)

include F chosen lead paid E pegs near in
theorem original {g : ℝ→ℝ} (coupling : Coupling G g) (q : ℕ) {ε : ℝ} (he : 0<ε) :
    ∃e:ℕ,∀ᶠr in trail,∃a:R.family.label 4,master L 4 r a=J r 4 (stepField R.family) ∧
      (∀N p,L.level r≤N→quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) a)≤
        R.family.S.a (L.level r)^4*(R.family.path.levels.clock.hatBeta (L.level r)^e*‖stepField R.family‖)) ∧
      ∀(b:R.family.label 4) (φ:Test 2) (cut:(N p:ℕ)→Fin (N+1)),
        let central:=S.representative 4 (J r 4 (stepField R.family))
        let exterior:=S.representative 4 (master L 4 r b)
        ∀ᶠz in U,‖profile R cut (atRef L 4 r z a) (atRef L 4 r z b) φ z.1 z.2-
          profile R cut central exterior φ z.1 z.2‖≤ε*(g r)^q := by
  obtain ⟨e,market⟩:=WilsonReportingMeasuredTender.entry B E
    (WilsonReportingMeasuredAdmission.present F J lead paid) pegs near 4
  refine ⟨e,?_⟩
  filter_upwards [market,pegs.level.growing.eventually_ge_atTop (R.family.ref 4),coupling.positive] with r bought live gr
  obtain ⟨a,cost,name⟩:=bought (stepField R.family)
  refine ⟨a,name,fun N p hN=>?_,?_⟩
  · rw [WilsonMatrixTicketLanesReportedAdmission.quota R F L 4 r a live N p hN]
    exact mul_le_mul_of_nonneg_left cost (pow_nonneg (R.family.S.a_pos _).le _)
  intro b φ cut central exterior
  have zero:=measured F L chosen live a b φ cut
  dsimp only at zero
  rw [name] at zero
  filter_upwards [Metric.tendsto_nhds.mp zero (ε*(g r)^q) (mul_pos he (pow_pos gr _))] with z hz
  simpa only [dist_zero_right] using hz.le

end YM.Integration.WilsonInvariantActionDoubleAdmission
