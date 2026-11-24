import YM.Integration.WilsonMaxwellThermometerSignedWallet
/-! The native joint-cell public response on three moving solved arrays,
with their genuine engineering factors and all proper filed faces. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSolvedSlope
open Function Set Filter Finset Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonMaxwellThermometerFirstDetector WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerPublicStation WilsonMaxwellThermometerSignedWallet WilsonMaxwellThermometerChargedHeads
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(s:ℝ→ℕ)

theorem received (r:ℝ)(z:ℕ×ℕ)(hr:0<r)(simple:G.Simple)(stage:V.Meets W (WilsonMaxwellThermometerSignedWallet.board R (s r) r z.2) 6)
    (v:∀i,Axes R i):
    report R W K s r z (deposited R (s r) r z.2 v)=report R W K s r z (store R (maximalPaid R r v)):=by
  by_cases fine:s r≤z.1
  · simp only [report,dif_pos fine]
    apply Finset.sum_congr rfl
    intro o _
    exact congrArg _ (changed R W (s r) r z.2 hr simple stage _ v)
  · simp only [report,dif_neg fine]

theorem referenced (r:ℝ)(z:ℕ×ℕ)(simple:G.Simple)(stage:V.Meets W (WilsonMaxwellThermometerSignedWallet.board R (s r) r z.2) 6):
    report R W K s r z (store R (maxpart R (target R)))=report R W K s r z (Rose.tag G):=by
  rw [←oriented R]
  by_cases fine:s r≤z.1
  · simp only [report,dif_pos fine]
    apply Finset.sum_congr rfl
    intro o _
    let m:=WilsonMaxwellThermometerSignedWallet.board R (s r) r z.2
    let x:=translated m (Mesh.back m ((R.family.S.toDepth fine z.2).parent ∘ o))
    exact congrArg (fun b:ℂ=>weight (Rose.test K) (positions (R:=R) r z) o • b)
      (WilsonMaxwellThermometerSignedWallet.trim R W x simple stage (target R)).symm
  · simp only [report,dif_neg fine]

variable {f:Extraction.Order}{U:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}{S:Table R.family.book}
variable (A:ℝ→Group R.family 6)(J:ℝ→tower S)
local notation "k" => fun r=>(A r).station.k
local notation "cut" => trail.curry (U:Filter (ℕ×ℕ))
theorem original (simple:G.Simple)(book:Book (f:=f) (l:=U) (H:=H) A J)(prior:(U:Filter _)≤f.fuse)
    (v:ℝ×(ℕ×ℕ)→∀i,Axes R i)
    (fit:∀i,Tendsto (fun w=>maximalPaid R w.1 (v w) i) cut (𝓝 (maxpart R (target R) i))):
    Tendsto (fun w:ℝ×(ℕ×ℕ)=>report R W K k w.1 w.2 (deposited R (k w.1) w.1 w.2.2 (v w)))
      cut (𝓝 ((Rose.c_T K:ℝ):ℂ)):=by
  have small:=(WilsonMaxwellThermometerPublicCollege.funding R A J simple book).1
  have academic:∀ᶠ w:ℝ×(ℕ×ℕ) in cut,0<w.1 ∧ V.Meets W (WilsonMaxwellThermometerSignedWallet.board R (k w.1) w.1 w.2.2) 6:=by
    apply eventually_curry_iff.mpr
    filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi 0),
      WilsonMaxwellThermometerPublicCollege.voted R W (V:=V) A J simple book] with r hr voted
    exact .of_forall fun z=>⟨hr,voted z.2⟩
  haveI:NeBot cut:=by
    constructor
    intro dead
    have lost:∀ᶠ _w:ℝ×(ℕ×ℕ) in cut,False:=by rw [dead];exact Filter.eventually_bot
    obtain ⟨r,absurd⟩:=(eventually_curry_iff.mp lost).exists
    exact absurd.exists.choose_spec
  have anchored:smeared W K (store R (maxpart R (target R)))=smeared W K (Rose.tag G):=by
    apply tendsto_nhds_unique ((fixed R W K k f U prior small _).congr' ?_)
      (fixed R W K k f U prior small (Rose.tag G))
    filter_upwards [academic] with w h
    simpa only [quotient] using referenced R W K k w.1 w.2 simple h.2
  have moved (i:Fin 3):Reads 6 (F:=cut)
      (fun w=>store R (maximalPaid R w.1 (v w)) i) (store R (maxpart R (target R)) i):=by
    let L:=(tableD G 6).toLinearMap ∘ₗ ((up (Nat.le_of_lt_succ (grade i).isLt)) ∘ₗ
      (sector (R.family.labels.level (grade i)))).restrictScalars ℝ
    exact L.continuous_of_finiteDimensional.continuousAt.tendsto.comp (fit i)
  rw [←WilsonMaxwellThermometerFirstDetector.normalized W K simple,←anchored]
  refine (lights 6 _ _ moved _ (smeared W K) (fixed R W K k f U prior small)).congr' ?_
  filter_upwards [academic] with w h
  simp only [quotient]
  exact (received R W K k w.1 w.2 h.1 simple h.2 (v w)).symm

end YM.Integration.WilsonMaxwellThermometerSolvedSlope
end
