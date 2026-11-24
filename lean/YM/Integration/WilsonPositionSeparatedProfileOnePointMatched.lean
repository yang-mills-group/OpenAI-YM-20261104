import YM.Integration.WilsonPositionSeparatedProfileOnePointDressing
import YM.FVA2.Main

/-! Exact all-orders matching of the signed noninvariant part of a genuine
one-point insertion. Both physical changes of frame may vary with length. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileOnePointMatched
open Function Filter Set Finset Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Pert Pert.Position Lattice Maxwell Maxwell.Free XSpace XSpace.Normalize
open MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale
open scoped Classical Topology BigOperators
variable {G : Gauge} (C : Family G)

def adjusted (d : ℕ) (a : Change G d) : (Bel C.book).Field d≃ₗ[ℂ](Bel C.book).Field d :=
  if h : Bijective (stand a) then
    (fields C.labels d).trans ((LinearEquiv.ofBijective _ h).trans (fields C.labels d).symm)
  else LinearEquiv.refl ..

theorem rotate (d : ℕ) (a : Change G d) (s : Signed) (w : (Bel C.book).Field d) :
    adjusted C d a ((Bel C.book).mirror (spin_free C.labels) d s w)=
      (Bel C.book).mirror (spin_free C.labels) d s (adjusted C d a w) := by
  unfold adjusted
  split_ifs with h
  · apply (fields C.labels d).injective
    simp only [WilsonPositionSeparatedProfileOnePointWave.free,LinearEquiv.trans_apply,LinearEquiv.ofBijective_apply,
      LinearEquiv.apply_symm_apply]
    rw [WilsonPositionSeparatedProfileOnePointWave.free C d s w]
    exact (stood_ori a s ((fields C.labels d) w)).symm
  · rfl

variable {C} {o : Extraction.Order} {U : Table C.book} (F : Final C o U) (J : ℝ→tower U)

theorem physical (lead : Leading F J) (d : ℕ) (a b : ℝ→Change G d) (s : Signed) (v : Sec G d) :
    ∀ᶠr in trail,∀(p : Viewers F)(x : Points 1),
      U.classMoment (spectator F p) (fun _=>d) (r • x)
        (fun _=>J r d (adjusted C d (b r) (adjusted C d (a r) ((fields C.labels d).symm (v-ori s.ortho d v)))))=0 := by
  filter_upwards [lead.equivariant d] with r good p x
  have spun : (fields C.labels d).symm (ori s.ortho d v)=
      (Bel C.book).mirror (spin_free C.labels) d s ((fields C.labels d).symm v) := by
    apply (fields C.labels d).injective
    rw [LinearEquiv.apply_symm_apply,WilsonPositionSeparatedProfileOnePointWave.free,LinearEquiv.apply_symm_apply]
  simp_rw [map_sub,spun,rotate,good.1 s]
  exact WilsonPositionSeparatedProfileOnePointSpin.all_states F d s (r • x) _ p

private theorem single (x : Points 1) : x∈conf 1:=fun i j _=>Subsingleton.elim i j

theorem exact (simple : G.Simple) (lead : Leading F J) (Z : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {P : Prescription (Press.portDeck G)}
    {dial : Bool} (named : Main.Match Z simple M P dial) (d : ℕ) (a b : ℝ→Change G d)
    (s : Signed) (v : Sec G d) (ν : ℝ) (φ : Test 1) :
    ∀ᶠr in trail,∀(p : Viewers F)(order : ℕ)(θ : ℝ),
      φ.applyTo (fun x=>U.classMoment (spectator F p) (fun _=>d) (r•x)
        (fun _=>J r d (adjusted C d (b r) (adjusted C d (a r) ((fields C.labels d).symm (v-ori s.ortho d v))))))=
        ∑k∈range (order+1),(θ:ℂ)^k * φ.applyTo (fun x=>
          Facets.actMark (Measure.Z Z.scheme Z.criterion ν M d)
            (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M d)) 1 ⟨x,single x⟩ k (fun _=>v-ori s.ortho d v)) := by
  filter_upwards [physical F J lead d a b s v] with r observed p order θ
  have formal (x : Points 1) (k : ℕ) : Facets.actMark (Measure.Z Z.scheme Z.criterion ν M d)
      (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M d)) 1 ⟨x,single x⟩ k (fun _=>v-ori s.ortho d v)=0 :=
    WilsonPositionSeparatedProfileOnePointDressing.coefficient C simple M ν _ (named.frame ν d).1 _ s _ k v
  simp_rw [observed p,formal]
  simp [Test.applyTo]

end YM.Integration.WilsonPositionSeparatedProfileOnePointMatched
