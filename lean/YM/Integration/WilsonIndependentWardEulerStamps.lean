import YM.Integration.WilsonIndependentWardCoverDirection

/-! The two actual local Ward words for the Euler direction. The reflected
half of the action is included before identifying its local representative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardEulerStamps
open Finset Function Gauge Lattice RG Source WardBin Wilson
open FormalOPE.RG10.InversionWard RegulatorIR RegulatorIR.Profiles
open scoped Classical Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}(d:Axis)
def boot (d:Axis)(w:Lattice.Step): Walk:=oriented (posDir d) w
def scope (d:Axis) := insert (0:Cover) ((univ (α:=Axis)).biUnion fun i=>
    (visits (0:Cover) (boot d (posDir i))).toFinset ∪ (visits (0:Cover) (boot d (negDir i))).toFinset)
def b : Edge Cover := (0,d)
def vector (V:CoverConfig G) : G.Color:=euler V (b d)
def energy (V:CoverConfig G) : ℝ:=⟪vector d V,vector d V⟫_ℝ
def discharge : CoverConfig G→ℝ:=WilsonIndependentWardCoverDirection.emission (b d) (vector d)

theorem supported : LocalOn (scope d : Set Cover) (vector (G:=G) d) := by
  intro X Y h
  unfold vector b euler
  apply sum_congr rfl
  intro i hi
  have face (v:Lattice.Step)(hm:(visits (0:Cover) (boot d v)).toFinset ⊆ scope d) :
      G.curvature (WardBin.wheel (b d) v X)=G.curvature (WardBin.wheel (b d) v Y) :=
    congr_arg _ (travel_local (0:Cover) (boot d v) _ _ (fun i ha hb=>
      h i (hm (List.mem_toFinset.mpr ha)) (hm (List.mem_toFinset.mpr hb))))
  apply congr_arg₂ (·+·)
  · exact face _ (fun x hx=>mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ i,mem_union_left _ hx⟩))
  · exact face _ (fun x hx=>mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ i,mem_union_right _ hx⟩))

theorem folded (o:Site n) : places o (vector (G:=G) d)=fun U=>euler U (edgeAt (b d) o) := by
  funext v
  exact euler_at v o 0 d
theorem printed (o:Site n) : Proxy (places o (vector (G:=G) d)) := by
  rw [folded]
  exact proxy_force _

def observable (a:G.Color)(v:CoverConfig G) := ⟪a,vector d v⟫_ℝ
theorem inner_local (a:G.Color) : LocalOn (scope d:Set Cover) (observable d a) := by
  intro U V eq
  exact congrArg (fun x=>⟪a,x⟫_ℝ) (supported d _ _ eq)
theorem root : (b d).1∈scope d := mem_insert_self ..
theorem folded_trace (o:Site n)(fit:FitsIn (scope d) n) :
    places o (discharge (G:=G) d) = ∑ i:G.ColorIndex,
      slope (edgeAt (b d) o) (dirs G i) (places o (observable d (dirs G i))) := by
  ext U
  rw [Finset.sum_apply]
  change (∑ i:G.ColorIndex,slope (b d) (dirs G i) (observable d (dirs G i)) (expandAt o U)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (slopes_at (inner_local d (dirs G i)) fit o (root d) (dirs G i)).symm U
theorem covariant (t:Cover → G.El)(v:CoverConfig G) :
    vector d (Lattice.gauge t v)=G.adjoint (t (b d).1) (vector d v) := euler_gauge ..

theorem original : LocalStamp (fun _=>energy (G:=G) d) 0 ∧ LocalStamp (fun _=>discharge (G:=G) d) 0 := by
  obtain ⟨N,fit⟩:=someFits (scope d)
  have A:=printed (G:=G) d (0:Site N)
  have line:=WilsonIndependentWardCoverDirection.regular (vector (G:=G) d) (supported d) (0:Site N) fit A (b d)
  constructor
  · apply WilsonIndependentWardLocalStamp.original _ (scope d) _ _ N 0 fit
    · exact (A.pair A).after (fun v=>⟪v.1,v.2⟫_ℝ) (contDiff_fst.inner ℝ contDiff_snd)
    · intro U V H
      exact congrArg (fun v=>⟪v,v⟫_ℝ) (supported d _ _ H)
    · intro t U
      unfold energy
      rw [covariant]
      exact (WardBin.adjointGauge (t (b d).1)).inner_map_map ..
  · apply WilsonIndependentWardLocalStamp.original _ (scope d) _ _ N 0 fit
    · rw [folded_trace d 0 fit]
      exact Proxy.sum _ (fun i _ =>WilsonIndependentWardSingleSlope.scalar _ (A.after _ (innerSL ℝ (dirs G i)).contDiff) _)
    · intro U V H
      change (∑ i:G.ColorIndex,slope (b d) (dirs G i) (observable d (dirs G i)) U) = ∑ i:G.ColorIndex,slope (b d) (dirs G i) (observable d (dirs G i)) V
      exact Finset.sum_congr rfl (fun i _=>slopes_cover (inner_local d (dirs G i)) (root d) (dirs G i) U V H)
    · exact WilsonIndependentWardCoverDirection.invariant (b d) (vector d) line (covariant d)

end YM.Integration.WilsonIndependentWardEulerStamps
