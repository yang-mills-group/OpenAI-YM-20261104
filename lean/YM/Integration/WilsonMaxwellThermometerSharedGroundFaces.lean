import YM.Integration.WilsonMaxwellThermometerReleasedSection

/-! On the actual public cell, use the complete ground term of the original
finite inversion with exactly the Galop source coefficients on every face.
The difference pays the original section against its separately prepared
regulator section at the same position, before centering. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSharedGroundFaces
open Filter Function Set Finset Lattice Labels Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Photo
open XSpace.Tornado XSpace.AxesTangent XSpace.Retirement PhysicalNext.Repeat.Legato RG RG.Supply Org Input
open RegulatorIR RegulatorIR.FVAAlt2 WilsonThermometerPositionTunedPublicCharge WilsonThermometerPositionTunedGalop
open WilsonMaxwellThermometerInteracting Wilson XSpace.Rose Precision PertExtension PertExtension.Orb
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(D:ChartRatio G)(W:Initialize G){V:Normalize.Store G}(x:Sample 3)(p:Tags G 6 3)

theorem zeroed (read:Tags G 6 3 → Finset (Fin 3) → PowerSeries ℂ)(S:Badge):
    filed W (V:=V) x p 0 S read = PowerSeries.coeff 0
      (read (pulseU (0:Days 3) (deck (V.layout W (grab x) 6)) p) S):=by
  have no (f:Days 3)(h:f∈tally 0 3):f=0:=by
    ext1 j
    exact Nat.eq_zero_of_le_zero (((totaled f).mp h) ▸
      Finset.single_le_sum (f:=fun i=>f i) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j))
  unfold filed
  rw [Finset.sum_eq_single 0]
  · simp
  · intro a ha ne
    exact (ne (no a ha)).elim
  · intro h
    exact (h ((totaled (0:Days 3)).mpr (by simp))).elim

def tree (S:Badge):ℂ:=
  let q:=pulseU (0:Days 3) (deck (V.layout W (grab x) 6)) p
  ∑a:Picked R 6 S,WilsonThermometerPositionTunedPublicCharge.charge R W 6 x q S a *
    (YM.FVAAlt2.Fixed.treeMom D
      (WilsonPositionProgramCopyTop.planted R x.F.p (fun j:S=>(a j).1.val)
        (fun j=>x.layout j.val) (fun j=>(a j).2))
      (Kick.depthF Finset.univ (fun j:S=>(a j).1.val) (fun j=>(a j).2)) 0:ℝ)

theorem emitted (law:LocalRatio D)(S:Badge):
    originalRead R W (V:=V) x p 0 S=tree R D W (V:=V) x p S:=by
  rw [originalRead,zeroed]
  simp only [tree,submitted,map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun w:ℂ=>_ * w)
  unfold loan WilsonThermometerPositionTunedSlope.finite
  rw [PowerSeries.coeff_mk]
  exact WilsonPositionProgramCopyTop.original R x.F.p _ _ _ D law (W.tree x.F.p) 0

theorem reported (law:LocalRatio D)(S:Badge):
    tree R D W (V:=V) x p S - WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p 0 S =
      PowerSeries.coeff 0 (signed R W 6 x (pulseU (0:Days 3)
        (deck (V.layout W (grab x) 6)) p) S):=by
  rw [←emitted R D W x p law]
  exact (WilsonThermometerPositionTunedGalop.face R W x p 0 S).trans
    (zeroed W x p _ S)

end YM.Integration.WilsonMaxwellThermometerSharedGroundFaces
