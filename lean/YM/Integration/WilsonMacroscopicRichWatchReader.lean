import YM.Integration.WilsonMacroscopicRichFixedWatchSale
import YM.Integration.PhysicalOPEApproximation

/-! One finite set of physical macroscopic watches hears the original Reader packet. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchReader
open Set Filter Function Spec OPE OPE.Orbits PhysMS Next.UVStress
open scoped BigOperators Topology Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {I:Type}[Fintype I]{d:I→ℕ}

def exterior (S:Table C.book)(W:Watch C):ExteriorData S:=
  classes S (S.classTokens ∘ W.q) (Points.tail W.held)

theorem admitted (S:Table C.book)(W:Watch C):Apt (exterior S W):=by
  have move:Points.across (-(W.held 0)) W.held=W.held:=by
    rw [W.origin,neg_zero]
    ext i
    simp [Points.across]
  simpa only [exterior,move] using classes_apt W.held W.wild (S.classTokens ∘ W.q)

theorem same (W:Watch C)(h:ℕ)(z:S.Field h):
    witnessAt S h (exterior S W) z=W.tester S h z:=by
  rw [exterior,witness_classes,Watch.test_known]
  have points:Points.cons 0 (Points.tail W.held)=W.held:=by
    ext1 i
    refine Fin.cases ?_ (fun _=>?_) i
    · exact W.origin.symm
    · rfl
  rw [points]
  rfl

def detector {a h:ℕ} (W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ] S.Field h)
    (fits:∀z,D (fun i=>(W i).tester S h z)=z):Detector S h where
  size:=a
  listen i:=exterior S (W i)
  awake i:=admitted S (W i)
  report:=D.toLinearMap
  recovered z:=by
    change D (fun i=>witnessAt S h (exterior S (W i)) z)=z
    simp only [same]
    exact fits z

def current {a:ℕ}(W:Fin a→Watch C)(x:I→E4)(v:Labels S d)(i:Fin a):ℂ:=
  let e:=exterior S (W i)
  whole S x v (positions S e).ofLp (fun j=>(tags S e j).2)

theorem original (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(h:ℕ) :
    ∃a:ℕ,∃W:Fin a→Watch C,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,
      (∀z,D (fun i=>(W i).tester S h z)=z) ∧
      ∀(v:(j:I)→(Climb.Bel C.book).Field (d j))(M η ε:ℝ),0≤M→0<η→0<ε→
      ∀ᶠ r in Trace.Pilot.trail,∀x:I→E4,WithinRoom r M η x 0→
      ‖D (current W x (Frame.born J r v))-R.packet h x (Frame.born J r v) 0‖
        ≤‖D‖*r^((h:ℝ)+1-ε):=by
  obtain ⟨a,W,D,fits⟩:=WilsonMacroscopicRichFixedWatchSale.select F h
  refine ⟨a,W,D,fits,?_⟩
  intro v M η ε hM hη hε
  let E:=detector W D fits
  filter_upwards [detectorOPE_power F R J leading foundation v M η hM hη E ε hε,
    self_mem_nhdsWithin] with r estimate pos x room
  let z:=R.packet h x (Frame.born J r v) 0
  let y:=current W x (Frame.born J r v)
  let heard:=fun i=>(W i).tester S h z
  have each:‖y-heard‖≤r^((h:ℝ)+1-ε):=by
    refine (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg (le_of_lt pos) _)).2 fun i=>?_
    have hi:=estimate x room i
    change ‖y i-witnessAt S h (exterior S (W i)) z‖≤_ at hi
    change ‖y i-(W i).tester S h z‖≤_
    rw [same] at hi
    exact hi
  change ‖D y-z‖≤_
  rw [←fits z,←map_sub]
  exact (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left each (norm_nonneg _))

end YM.Integration.WilsonMacroscopicRichWatchReader
