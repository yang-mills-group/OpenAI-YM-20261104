import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellConservationPivots
import YM.Maxwell.Reorder
import YM.Next.MAXWELL.Mark

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation
open YM YM.Maxwell YM.Maxwell.Free YM.Maxwell.Wick YangMills MeasureTheory Set
open H7IndependentIntegratedMaxwellWardPupils H7IndependentFiledMaxwellConservationPivots
open H7StandaloneAppointedPublicWardRows H7StandaloneFourSmearedWardReadings
open YM.XSpace.Normalize (Index left right)
open YM.UVNext.FreeStress.PublicPanels (planeLabel)
open YM.StressFlux (onePoint onePoint_at onePoint_prod head head_at)
open scoped Topology ContDiff BigOperators

theorem onePhi (G : Gauge) (x : YM.Points 1) (a b i l : YM.Axis) :
    onePoint x (phi (G:=G) a b i l) = 0 := by
  rw [phi,map_sum]
  apply Finset.sum_eq_zero
  intro c _
  exact onePoint_prod (omegaLeg c a i) (omegaLeg c b l) x

theorem oneSheet (G : Gauge) (x : YM.Points 1) (a b : YM.Axis) :
    onePoint x (sheetEnergy (G:=G) a b) = 0 := by simp [sheetEnergy,onePhi]

theorem oneStress (G : Gauge) (x : YM.Points 1) (a b : YM.Axis) :
    onePoint x (polStress G a b) = 0 := by simp [polStress,oneSheet]

theorem oneSquare (g : GaugeGroup) (H : g.core.Simple) (x : YM.Points 1) (k : Index) :
    onePoint x (square H k).val = 0 := by
  change onePoint x (XSpace.Normalize.label g.core k k)=0
  rw [← planeLabel]
  exact onePhi g.core x _ _ _ _

theorem vacuumAt (g : GaugeGroup) (H : g.core.Simple) (k : Fin 4) (x : YM.Points 1) :
    moment g.core x (fun _ => (columns H 0 0 k).val) = if k=0 then 1 else 0 := by
  fin_cases k
  · exact constants x
  · change moment g.core x (fun _ => sheetEnergy 0 0)=0
    rw [← onePoint_at,oneSheet]
  · change moment g.core x (fun _ => (∑ t : Index, square H t).val)=0
    rw [← onePoint_at,Submodule.coe_sum]
    exact (map_sum (onePoint (G := g.core) x) (fun i : Index => ((square H i).val : WickPol g.core))
      Finset.univ).trans (Finset.sum_eq_zero fun t _ => oneSquare g H x t)
  · change moment g.core x (fun _ => -polStress g.core 0 0)=0
    rw [← onePoint_at,map_neg,oneStress,neg_zero]

theorem vacuumRow (g : GaugeGroup) (H : g.core.Simple)
    (hK : 0 < H7IndependentFiledMaxwellProfiles.price g.core) (k : Fin 4) :
    (∫ x : YM.Points 1, (pupils (H7IndependentFiledMaxwellProfiles.price g.core) hK).vacuum x *
      moment g.core x (fun _ => (columns H 0 0 k).val)) = if k=0 then 1 else 0 := by
  simp_rw [vacuumAt g H k]
  by_cases h : k=0
  · simp only [if_pos h,mul_one]
    change (∫ x : YM.Points 1, ((oneMass x : ℝ) : ℂ))=1
    rw [integral_complex_ofReal,normalized.2]
    norm_num
  · simp [h]

theorem unitProbe (g : GaugeGroup) (H : g.core.Simple) (j : Fin 2) (x : YM.Points 2) :
    moment g.core x ![1,(probes H j).val]=0 := by
  let t : YM.Points 1 := points (fun _ => x 1)
  have ht : t ∈ conf 1 := by
    change Function.Injective t.ofLp
    intro i l _
    exact Subsingleton.elim i l
  have hx : YM.Points.cons (x 0) t=x := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> rfl
  have hp : Fin.cons (1 : WickPol g.core) (fun _ : Fin 1 => (probes H j).val) =
      (![1,(probes H j).val] : Fin 2 → WickPol g.core) := by funext i; fin_cases i <;> rfl
  have h := adjoin ht (x 0) (fun _ : Fin 1 => (probes H j).val)
  rw [hx,hp] at h
  rw [← h,← onePoint_at]
  fin_cases j
  · exact oneSquare g H t 5
  · exact oneSquare g H t 0

theorem offAxis (g : GaugeGroup) (H : g.core.Simple) (j : Fin 2) {a : YM.Axis} (ha : a≠0)
    (k : Fin 4) (hk : k≠3) (x : YM.Points 2) :
    moment g.core x ![(columns H a 0 k).val,(probes H j).val]=0 := by
  rw [← head_at]
  have h : (columns H a 0 k).val=0 := by
    fin_cases k <;> simp_all [columns]
  rw [h]
  exact (head x ((probes H j).val : WickPol g.core)).map_zero

theorem unitAt (g : GaugeGroup) (H : g.core.Simple) (j : Fin 2) (a : YM.Axis) (x : YM.Points 2) :
    moment g.core x ![(columns H a 0 0).val,(probes H j).val]=0 := by
  by_cases h : a=0
  · subst a; exact unitProbe g H j x
  · exact offAxis g H j h 0 (by decide) x

theorem stressDivergence (g : GaugeGroup) (H : g.core.Simple) (j : Fin 2)
    {x : YM.Points 2} (hx : x ∈ conf 2) :
    (∑ a : YM.Axis, YM.Points.gradient 0 a (fun z =>
      moment g.core z ![-polStress g.core a 0,(probes H j).val]) x)=0 := by
  have entry (a : YM.Axis) : YM.Points.gradient 0 a (fun z =>
      moment g.core z ![-polStress g.core a 0,(probes H j).val]) x =
      head x (probes H j).val (-(rewired (glide g.core (basis a)) (polStress g.core a 0))) := by
    rw [positionD _ hx,head_at]
    apply congrArg (moment g.core x)
    funext i
    fin_cases i <;> simp [Function.update]
  simp_rw [entry]
  rw [← map_sum,Finset.sum_neg_distrib,pol_conservation,neg_zero,map_zero]

theorem testedStress (g : GaugeGroup) (H : g.core.Simple) (j : Fin 2) (φ : SeparatedTest 2) :
    (∑ a : YM.Axis, ∫ x : YM.Points 2, YM.Points.gradient 0 a (fun z => φ z) x *
      moment g.core x ![-polStress g.core a 0,(probes H j).val])=0 := by
  let m (a : YM.Axis) (z : YM.Points 2) := moment g.core z ![-polStress g.core a 0,(probes H j).val]
  have h (a : YM.Axis) := testedByParts (m a) (fun _ hx => moment_smooth _ hx)
    φ (YM.Points.direction 0 a)
  have eqn (a : YM.Axis) : (∫ x : YM.Points 2, YM.Points.gradient 0 a (fun z => φ z) x * m a x) =
      -(∫ x : YM.Points 2, φ x * YM.Points.gradient 0 a (m a) x) := ((congrArg Neg.neg (h a).2).trans (neg_neg _)).symm
  change (∑ a : YM.Axis, ∫ x : YM.Points 2, YM.Points.gradient 0 a (fun z => φ z) x * m a x)=0
  simp_rw [eqn]
  rw [Finset.sum_neg_distrib]
  have summed : (∑ a : YM.Axis, ∫ x : YM.Points 2, φ x * YM.Points.gradient 0 a (m a) x) =
      (∫ x : YM.Points 2, ∑ a : YM.Axis, φ x * YM.Points.gradient 0 a (m a) x) :=
    (integral_finset_sum Finset.univ (fun a _ => (h a).1)).symm
  rw [summed]
  have point (x : YM.Points 2) : (∑ a : YM.Axis, φ x * YM.Points.gradient 0 a (m a) x)=0 := by
    rw [← Finset.mul_sum]
    by_cases hz : φ x=0
    · simp [hz]
    · exact (by rw [show (∑ a : YM.Axis, YM.Points.gradient 0 a (m a) x)=0 from
            stressDivergence g H j (φ.tsupport_subset' (subset_tsupport _ hz)),mul_zero])
  simp_rw [point]
  simp

def conservation (g : GaugeGroup) (H : g.core.Simple) (P : Pupils) (i : Fin 2) (k : Fin 4) : ℂ :=
  ∑ j : Fin 2, ∑ a : YM.Axis, ∫ x : YM.Points 2, YM.Points.gradient 0 a (fun z => P.conservation i j z) x *
    moment g.core x ![(columns H a 0 k).val,(probes H j).val]

theorem conservationRows (g : GaugeGroup) (H : g.core.Simple)
    (hK : 0 < H7IndependentFiledMaxwellProfiles.price g.core) (i : Fin 2) (k : Fin 4) :
    conservation g H (pupils (H7IndependentFiledMaxwellProfiles.price g.core) hK) i k =
      if k=(![1,2] : Fin 2 → Fin 4) i then -1 else 0 := by
  let P := pupils (H7IndependentFiledMaxwellProfiles.price g.core) hK
  have middle (l : Fin 2) : conservation g H P i ((![1,2] : Fin 2 → Fin 4) l) =
      if i=l then -1 else 0 := by
    rw [conservation,← signedConservation g H hK i l]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_eq_single 0
    · intro a _ ha
      have hk : ((![1,2] : Fin 2 → Fin 4) l)≠3 := by fin_cases l <;> decide
      simp_rw [offAxis g H j ha _ hk]
      simp
    · simp
  fin_cases k
  · have zero : conservation g H P i 0 = 0 := by
      unfold conservation
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro a _
      calc
        _ = ∫ _ : YM.Points 2, (0 : ℂ) := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact (congrArg (fun z : ℂ => YM.Points.gradient 0 a (fun y => P.conservation i j y) x * z)
            (unitAt g H j a x)).trans (mul_zero _)
        _ = 0 := by simp
    calc
      _ = 0 := zero
      _ = _ := by
        have h0 : (0 : Fin 4) ≠ (![1,2] : Fin 2 → Fin 4) i := by fin_cases i <;> decide
        exact (if_neg h0).symm
  · have h := middle 0
    fin_cases i <;> simpa [P] using h
  · have h := middle 1
    fin_cases i <;> simpa [P] using h
  · change (∑ j : Fin 2, ∑ a : YM.Axis, ∫ x : YM.Points 2, YM.Points.gradient 0 a
       (fun z => P.conservation i j z) x * moment g.core x ![-polStress g.core a 0,(probes H j).val]) = _
    simp_rw [testedStress g H]
    fin_cases i <;> simp

end PhysicalMatching.H7IndependentFiledMaxwellVacuumConservation
