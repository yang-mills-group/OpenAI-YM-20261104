import YM.Integration.WilsonPositionThermometerGradedReading
import YM.Integration.WilsonOriginalStationLaurent
import YM.Integration.WilsonOriginalStarFlagPrice

/-! The three actual inverse-fitted fields have a jointly paid window on their
own reporting station before the upper cutoff and period. The station's
horizon may be chosen after the date threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalThermometerPalette
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}

def levels (i : Fin 3) : ℕ := (grade i).val
abbrev disks (_ : Fin 3) : Set ℂ := {z | ‖z‖ ≤ 1}
def probe (i : Fin 3) (x : Wallet disks) : ℂ := (x i).val

theorem attentive (i : Fin 3) : Attn (fun _ : Fin 3=> (⊥:Submodule ℂ ℂ)) disks {i} (probe i):=by
  refine ⟨fun x y eq=>congrArg Subtype.val (eq i (mem_singleton_self _)),?_,?_⟩
  · intro j hj x s t u a b hu
    obtain rfl:= mem_singleton.mp hj
    simpa only [probe,Function.update_self] using hu
  · intro j hj x hx
    obtain rfl:=mem_singleton.mp hj
    exact (Submodule.mem_bot ℂ).mp hx

def coordinates (A : Group R.family 6) (k N p : ℕ) (i : Fin 3) : R.family.label (levels i):=
  Price.awake R.family (index A (grade i)) k N p (A.station.wheel.atCut (N,p) (index A (grade i)) (vector A univ i))
def salary (A : Group R.family 6):=∑i:Fin 3,WilsonPositionThermometerStationNorm.cost R.family (levels i)*‖vector A univ i‖
private theorem nonneg (i : Fin 3) : 0 ≤ WilsonPositionThermometerStationNorm.cost R.family (levels i):=by
  unfold WilsonPositionThermometerStationNorm.cost
  positivity

theorem station (simple : G.Simple) (ε : ℝ) (eps : 0<ε) :
    ∀ᶠ k in atTop,∀ (A:Group R.family 6), A.station.k=k → A.station.checked f H A.horizon →
    ∀ (N p:ℕ),k<N → ∀i:Fin 3,(R.family.labels.level (levels i)).coeffSize (coordinates R A k N p i) ≤
       (R.family.path.levels.clock.hatBeta k)^ε * salary R A := by
  filter_upwards [eventually_all.mpr fun i:Fin 3=>WilsonPositionThermometerStationNorm.original
    (f:=f) (H:=H) simple R.makes (levels i) ε eps,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0] with k prices positive A date checked N p top i
  exact (prices i A.station (index A (grade i)) rfl date checked (vector A univ i) N p top).trans
    (mul_le_mul_of_nonneg_left (single_le_sum (f:=fun a:Fin 3=>WilsonPositionThermometerStationNorm.cost R.family
      (levels a)*‖vector A univ a‖) (fun j _=>mul_nonneg (nonneg R j) (norm_nonneg _)) (mem_univ i))
      (Real.rpow_nonneg positive _))

theorem original (simple : G.Simple) (ε : ℝ) (eps : 0<ε) :
    ∀ᶠ k in atTop,∀ (A:Group R.family 6), A.station.k=k → A.station.checked f H A.horizon →
    ∀ σ Ω : ℝ,1 ≤ Ω →
    let K:=(R.family.path.levels.clock.hatBeta k)^ε * salary R A
    let E:=max 1 ((1+K)*wallet R levels σ)
    let w:=fun _ : Fin 3=>(E*Ω)⁻¹
    ∀ (N p:ℕ), k<N → ∀ o:Fin 3→Site (R.family.side k p),
    let g:=Pert.Asymptotics.regulatorRun R.family N p k
    let P:= R.family.path.rep N p k
    let X:=rows R levels o σ g P.p.threshold (coordinates R A k N p) probe
    ∀ order count stage vac coarse : ℕ, Fintype.card (Fin 3) ≤ count → maximum R levels ≤ order →
      order+1 ≤ stage → order ≤ coarse → tariff R levels ≤ coarse →
      order+Fintype.card (Fin 3)*tariff R levels ≤ AllOrder.Burn.horizon vac+2 →
      Scene.Armada X w (fun _=>tariff R levels) σ Ω⁻¹ order count (Fintype.card (Fin 3)*tariff R levels) ∧
      Mentor.Cruise.Voter X σ order count stage vac coarse ∧
      Tableau (fun _ : Fin 3=> (⊥:Submodule ℂ ℂ)) disks X ∧
      (∀s:(Stock.census (Fin 3)).Mode, Poly.toll w s*(E*Ω)^s.val.card=1) ∧
      WilsonOriginalStarFlagPrice.extent R levels ≤ P.p.B := by
  filter_upwards [station R (f:=f) (H:=H) simple ε eps,WilsonOriginalStarFlagPrice.fit R levels simple,
    (Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop 0] with k paid fit pos A date checked σ Ω one K E w N p top o g P X order count stage vac coarse load available room future stamp cover
  have kpos : 0 ≤ K:= mul_nonneg (Real.rpow_nonneg pos _)
    (sum_nonneg fun i _=> mul_nonneg (nonneg R i) (norm_nonneg _))
  have band:g ≤ 2*P.p.threshold:=by
    have point:P.p=R.family.path.levels.budget k:=(R.makes.wilson.represents N p k top.le).vac
    rw [point]
    exact (RG04B.thresholdHat R.makes (p:=p) top.le).2
  obtain ⟨crew,votes,change⟩:=appointed R levels o σ g P.p.threshold (coordinates R A k N p) probe kpos
    (paid A date checked N p top) (ActualRunKernelPackets.regulator_pos R N p k top.le).le P.p.threshold_pos band one
    (fun i x=>(x i).property) order count stage vac coarse load available room future stamp cover
  exact ⟨crew,votes,WilsonOriginalStarSceneMasked.tests R levels o σ g P.p.threshold _ _ _ probe attentive,
    change,fit N p top.le⟩

end YM.Integration.WilsonOriginalThermometerPalette
