import YM.RG05Readout.Many.Release
import YM.RG05Readout.Records.Packet
import YM.Integration.ActualTrajectoryTransport

/-! All eight signed entries of three genuinely distinct submitted residents.
The empty entry is the actual Wilson vacuum on the same regulator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalResidentReadout
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Extra.Histories Push Local
open MergeProof Accent Menu RG05Readout RG05Readout.Many RG05Readout.Records
open RG05Readout.Address Extra.Trajectories
open scoped Classical Topology BigOperators
variable {W:Type}[DecidableEq W][Fintype W]{B B':Census W}{G:Gauge}

def alternatives (c:Fin 3→ℂ)(F:Finset (Fin 3)→ℂ):ℂ:=
  F univ - c 0*F {1,2} - c 1*F {0,2} - c 2*F {0,1}
  + (c 0*c 1)*F {2} + (c 0*c 2)*F {1} + (c 1*c 2)*F {0} - (c 0*c 1*c 2)*F ∅

def selector (entry:Finset (Fin 3)→B.Mode)(c:Fin 3→ℂ):Poly B→L[ℂ]ℂ:=
  Poly.get (entry univ) - c 0 • Poly.get (entry {1,2}) - c 1 • Poly.get (entry {0,2}) - c 2 • Poly.get (entry {0,1})
  + (c 0*c 1) • Poly.get (entry {2}) + (c 0*c 2) • Poly.get (entry {1}) + (c 1*c 2) • Poly.get (entry {0})
  - (c 0*c 1*c 2) • Poly.get (entry ∅)

omit [Fintype W] in
lemma read (entry:Finset (Fin 3)→B.Mode)(c:Fin 3→ℂ)(v:Poly B):
    selector entry c v=alternatives c (fun A=>v.part (entry A)):=rfl

def modes (z:Fin 3→W)(all:(univ.image z)∈B.choices)(A:Finset (Fin 3)):B.Mode:=
  ⟨A.image z,B.down all _ (Finset.image_mono z (Finset.subset_univ A))⟩

variable (C:Family G){N per j u:ℕ}
local notation "Y"=>C.path.rep N per

theorem birth_read (z:Fin 3→W)(different:Injective z)(all:(univ.image z)∈B.choices)
    (f:W→Goods G (C.side N per))(c:Fin 3→ℂ)(V:Config G (C.side N per)):
    selector (modes z all) c (birth B (Y N) f V)=
      ((Y N).eval V:ℂ)*∏i:Fin 3,(f (z i) V-c i):=by
  rw [read]
  have received(A:Finset (Fin 3)):
      ((birth B (Y N) f) V).part (modes z all A)=((Y N).eval V:ℂ)*(∏i∈A,f (z i) V):=by
    unfold birth Mach
    rw [Poly.part_smul,pass_fire]
    change ((Y N).eval V:ℂ)*(∏i∈A.image z,f i V)=_
    rw [Finset.prod_image (fun i _ l _ h=>different h)]
  simp_rw [received];simp [alternatives,Fin.prod_univ_succ];ring

omit [Fintype W] in
lemma restriction (entry:Finset (Fin 3)→B'.Mode)(inc:B'.choices⊆B.choices)(c:Fin 3→ℂ)(v:Poly B):
    selector entry c (narrow inc v)=selector (fun A=>route inc (entry A)) c v:=by
  rw [read,read];simp_rw [narrow_right]

private theorem credit {D:Type*}[NormedAddCommGroup D][NormedSpace ℝ D][CompleteSpace D]
    (I:Config G (C.side N per)→D)(integrable:Integrable I (prior G _))(L:D→L[ℝ]ℂ)(jn:j ≤ N):
    gust C.path N per N (fun U=>L (I U)) j jn=fun U=>L (gust C.path N per N I j jn U):=by
  induction jn using Nat.decreasingInduction with
  | self=>simp only [gust_base]
  | of_succ i hi ih=>
    rw [gust_step C.path N per N _ hi,ih];funext U
    rw [gust_step C.path N per N _ hi];unfold StepData.push
    have passed:=L.integral_comp_comm (StepData.push_slice (C.path.levels.transition_mass i per (C.path.β N per (i+1)))
      U _ (gust_live C.path N per N I integrable hi))
    simp_rw [L.map_smul] at passed
    exact passed

/-- Outside the three occupied names the full submitted program is unchanged.
All restrictions use the genuine inherited census. -/
theorem reported (z:Fin 3→W)(different:Injective z)(all:(univ.image z)∈B'.choices)
    (inc:B'.choices⊆B.choices)(f:W→Goods G (C.side N per))(c:Fin 3→ℂ)
    (paid:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(V:Config G (C.side j per)):
    actualTransport C (N:=N) (fun Z=>∏i:Fin 3,(f (z i) Z-c i)) jn V=
      ((Y j).eval V:ℂ)⁻¹*selector (modes z all) c (narrow inc (gust C.path N per N (birth B (Y N) f) j jn V)):=by
  let I:=birth B (Y N) f
  let L:=selector (modes z (inc all)) c
  have initial:(fun X:Config G (C.side N per)=>((Y N).eval X:ℂ)*(∏i:Fin 3,(f (z i) X-c i)))=
      fun X=>L (I X):=funext fun X=>(birth_read C z different (inc all) f c X).symm
  unfold actualTransport
  simp only [Complex.real_smul,Complex.ofReal_inv]
  rw [initial,restriction]
  have pass:=congrFun (credit C I paid (L.restrictScalars ℝ) jn) V
  exact congrArg (((Y j).eval V:ℂ)⁻¹*·) pass

/-- The whole joint source reaches the earlier positive Wilson law through one
signed raw table.  Its intermediate vacuum cancels on every configuration. -/
theorem original (made:C.Makes)(z:Fin 3→W)(different:Injective z)(all:(univ.image z)∈B'.choices)
    (inc:B'.choices⊆B.choices)(f:W→Goods G (C.side N per))
    (paid:Integrable (birth B (Y N) f) (prior G _))(jn:j ≤ N)(uj:u ≤ j)(U:Config G (C.side u per)):
    let c:=fun i:Fin 3=>actualTransport C (N:=N) (f (z i)) (uj.trans jn) U
    actualTransport C (N:=N) (fun Z=>∏i:Fin 3,(f (z i) Z-c i)) (uj.trans jn) U=
      ((Y u).eval U:ℂ)⁻¹*gust C.path N per j (fun V=>selector (modes z all) c
        (narrow inc (gust C.path N per N (birth B (Y N) f) j jn V))) u uj U:=by
  intro c
  let H:=fun Z:Config G (C.side N per)=>∏i:Fin 3,(f (z i) Z-c i)
  rw [←actualTransport_tower C made (le_refl N) H jn uj]
  change ((Y u).eval U)⁻¹ • gust C.path N per j (fun V=>(Y j).eval V • actualTransport C (N:=N) H jn V) u uj U=_
  simp only [Complex.real_smul,Complex.ofReal_inv]
  apply congrArg (((Y u).eval U:ℂ)⁻¹*·)
  apply congrArg (fun F=>gust C.path N per j F u uj U)
  funext V
  have nz:((Y j).eval V:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive made.wilson jn V).ne'
  rw [show actualTransport C (N:=N) H jn V=_ from reported C z different all inc f c paid jn V]
  field_simp [nz]

end YM.Integration.WilsonSeparatedOriginalResidentReadout
