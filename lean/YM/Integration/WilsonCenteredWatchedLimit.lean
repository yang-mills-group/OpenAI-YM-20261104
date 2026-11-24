import YM.Integration.WilsonCenteredWatchedCylinder

/-! Ordered continuum hearings of the cell-integrated near source on the actual
finite macroscopic detector. The Wilson denominator is shared across the joint
moment, and the same scalar test accompanies all of the external probes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredWatchedLimit
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonCenteredWatchedShape WilsonCenteredWatchedCylinder
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {n : ℕ} {f : Extraction.Order} {S : Table R.family.book}

private theorem supported (t : Test n) (K : Points n → ℂ) :
    (∫x in tsupport (t : Points n→ℂ),t x*K x)=t.applyTo K :=by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have h : t x = 0 :=by by_contra hn; exact hx (subset_closure hn)
  rw [h,zero_mul]

def reading (d:Fin n→ℕ) (w:∀j,R.family.label (d j)) (φ:Test n) (W:Watch R.family) (r:ℝ) :=
  φ.applyTo fun x=> S.read (joint W r x) (tags R d w W)

/-- The outer detector uses its exact original occupied positions, including
every retained spectator, throughout each fixed-period UV limit. -/
theorem original (F:Spec.Final R.family f S) (simple:G.Simple) (d:Fin n→ℕ)
    (w:∀j,R.family.label (d j)) (φ:Test n) (W:Watch R.family) :
    ∃ ρ > 0, ∀ r : ℝ, 0 < r → r < ρ → ∃ pred : ℕ → Prop,
      f.limits pred (fun N p=>moment (R.family.beta N p) (fun U=>
        cylinder R d (N,p) w (mass R φ r (N,p)) U * W.plot N p U))
      (reading (S:=S) R d w φ W r) :=by
  obtain ⟨ρ,hp,geometry⟩:=WilsonCenteredWatchedShape.original W φ
  refine ⟨ρ,hp,fun r hr hR=>?_⟩
  obtain ⟨clear,untied⟩:=geometry r hr hR
  let K := tsupport (φ : Points n→ℂ)
  obtain ⟨pred,adm,V,mesh,per⟩:=YM.FrontierTrace.Primary.Junction.junction_tail F
    (K:=K) (μ:=volume.restrict K) (tags R d w W) (joint W r) (φ : Points n→ℂ)
    (R.again simple).1.control (continuous_joint W r) φ.hasCompactSupport clear
    (ae_restrict_mem φ.hasCompactSupport.measurableSet) untied
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).restrict
  refine ⟨pred,adm,V,fun p hp=>?_,?_⟩
  · refine (mesh p hp).congr' ?_
    filter_upwards [f.mesh.cofinal.eventually_ge_atTop W.t] with k hk
    rw [supported]
    exact (WilsonCenteredWatchedCylinder.original R d w W φ r (p:=p) hk).symm
  · have endpoint : (∫x in K,φ x * S.read (joint W r x) (tags R d w W)) =
        reading (S:=S) R d w φ W r :=supported φ _
    rw [endpoint] at per
    exact per

/-- All probes share the same admitted periods, ultraviolet subsequence and
eventual radius. This is the vector tested by the original exterior decoder. -/
theorem panel (F:Spec.Final R.family f S) (simple:G.Simple) (d:Fin n→ℕ)
    (w:∀j,R.family.label (d j)) (φ:Test n) {a:ℕ} (W:Fin a→Watch R.family) :
    ∃ ρ > 0, ∀ r : ℝ, 0 < r → r < ρ → ∃ pred : ℕ → Prop,
      f.limits pred (fun N p=> WilsonMacroscopicRichFixedWatchSale.heard W (N,p)
        (cylinder R d (N,p) w (mass R φ r (N,p))))
      (fun i=>reading (S:=S) R d w φ (W i) r) :=by
  choose ρ pos price using fun i=>original R F simple d w φ (W i)
  let windows := insert 1 (Finset.univ.image ρ)
  let radius := windows.min' (Finset.insert_nonempty 1 _)
  have inside : radius∈windows:=Finset.min'_mem _ _
  have paid : 0 < radius :=by
    rcases Finset.mem_insert.mp inside with left|right
    · rw [left]; norm_num
    · obtain ⟨i,_,eq⟩:=Finset.mem_image.mp right
      rw [←eq]
      exact pos i
  refine ⟨radius,paid,fun r hr hR=>?_⟩
  have small (i) : r<ρ i :=hR.trans_le (Finset.min'_le _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)))
  choose pred ordered using fun i=>price i r hr (small i)
  choose V mesh vol using fun i=>(ordered i).2
  exact ⟨fun p=>∀i,pred i p,eventually_all.mpr (fun i=>(ordered i).1),
    (fun p i=>V i p),(fun p hp=>tendsto_pi_nhds.mpr (fun i=>mesh i p (hp i))),
    tendsto_pi_nhds.mpr vol⟩

end YM.Integration.WilsonCenteredWatchedLimit
