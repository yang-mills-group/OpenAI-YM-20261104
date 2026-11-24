import YM.Integration.WilsonMovingGaussianCoordinates
import YM.MSbar.Rolling.Arc

/-! The actual joint block potential and Haar action on the complete finite
forest, with the same original coarse field and independent free directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingJointAction
open Filter Set Function Lattice RG Wilson Precision Tree Exterior
open Push.Uniform FormalBulk08 Jets Reef Next.Free Next.SectorChange Work.F08 Stationary MSbar.Rolling
open scoped Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

def index : (Pine G S F ⊕ wire G c) ≃ Push.Uniform.Joint F G :=
  (Equiv.sumCongr (Reef.pines F).symm (WilsonMovingGaussianCoordinates.link G c).symm).trans
    (Equiv.sumComm _ _)

def joint (v : Positions (Push.Uniform.Joint F G)) : Rays (Pine G S F ⊕ wire G c) :=
  v ∘ index F

theorem fine (v : Positions (Push.Uniform.Joint F G)) :
    (offer G F (joint F v ∘ Sum.inl)) ∘ WilsonMovingGaussianCoordinates.link G f =
      stamp F G (pushG F v) := (WilsonMovingGaussianCoordinates.stored F (pushG F v)).symm

theorem noise (t : S.Choices) (v : Positions (Push.Uniform.Joint F G)) :
    Reef.clack S t (Reef.graft F (joint F v)) = pushChart F G t v := by
  have h := fine F v
  change noiseTaylor S (represent (tint G _ (pushF F v)))
    (represent (tint G _ ((offer G F (joint F v ∘ Sum.inl)) ∘
      WilsonMovingGaussianCoordinates.link G f))) t =
    noiseTaylor S (represent (tint G _ (pushF F v)))
      (represent (tint G _ (stamp F G (pushG F v)))) t
  rw [h]

theorem free (v : Positions (Push.Uniform.Joint F G)) :
    stand G F (joint F v ∘ Sum.inl) = tape (pushG F v) := by
  funext i
  ext j
  change pushG F v ((pines F).symm (pines F (i,j))) = pushG F v (i,j)
  rw [Equiv.symm_apply_apply]

theorem measure (O : ChartRatio G) (v : Positions (Push.Uniform.Joint F G)) :
    pay O (tape (pushG F v)) =
      O.scale^(Fintype.card F.Free) * sap F O (joint F v ∘ Sum.inl) := by
  unfold pay Reef.sap Work.F05.toll
  rw [free, Finset.prod_mul_distrib]
  simp

theorem jacobian (O : ChartRatio G) (hO : LocalRatio O) :
    swung F O =ᶠ[𝓝 (0 : Positions (Push.Uniform.Joint F G))]
      fun v => Real.log (Reef.sap F O (joint F v ∘ Sum.inl)) := by
  have hscale : 0<O.scale ^ Fintype.card F.Free := pow_pos hO.scale _
  have base : pay O (0 : LogArray G F.Free) = O.scale^(Fintype.card F.Free) := by
    simp [pay, hO.anchored]
  have anchor : joint F (0 : Positions (Push.Uniform.Joint F G)) ∘ Sum.inl = 0 := rfl
  have proj : ContinuousAt (fun v : Positions (Push.Uniform.Joint F G) => joint F v ∘ Sum.inl) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_apply (index F (.inl i)) 0
  have localReceipt : ContinuousAt (sap F O)
      (joint F (0 : Positions (Push.Uniform.Joint F G)) ∘ Sum.inl) := by
    rw [anchor]
    exact (sap_smooth F O hO).continuousAt
  have smooth : ContinuousAt (fun v : Positions (Push.Uniform.Joint F G) => sap F O (joint F v ∘ Sum.inl)) 0 :=
    localReceipt.comp (f:=fun v : Positions (Push.Uniform.Joint F G) => joint F v ∘ Sum.inl) proj
  have positive : 0 < (fun v : Positions (Push.Uniform.Joint F G) =>
      Reef.sap F O (joint F v ∘ Sum.inl)) 0 := by
    change 0 < Reef.sap F O (joint F (0 : Positions (Push.Uniform.Joint F G)) ∘ Sum.inl)
    rw [anchor, sap_root F O hO]
    norm_num
  have pos : ∀ᶠ v : Positions (Push.Uniform.Joint F G) in 𝓝 0, 0 < sap F O (joint F v ∘ Sum.inl) :=
    smooth.eventually (lt_mem_nhds positive)
  filter_upwards [pos] with v hv
  change Real.log (pay O (tape (pushG F v)))-Real.log (pay O (0 : LogArray G F.Free)) = _
  rw [measure,base,Real.log_mul hscale.ne' hv.ne']
  ring

end YM.Integration.WilsonMovingJointAction
end
