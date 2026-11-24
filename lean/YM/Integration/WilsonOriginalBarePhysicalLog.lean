import YM.Integration.WilsonOriginalStarGradedScene
import YM.Integration.WilsonOriginalStarSceneMasked
import YM.Integration.WilsonPositionThermometerStationBirth
import YM.Integration.WilsonOriginalBareMarkedSheet
import YM.Next.WARD_BIN.Printing

/-! The entire registered finite bare log on the original Wilson group field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBarePhysicalLog
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise Affinity
open Push.AbsoluteSums.Animals Next.Rank
open PhysicalNext.Repeat.Legato WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows
open WilsonOriginalStarSceneRead ActualRunPhysicalPages
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] [DecidableEq V] (d:V→ℕ)

omit [Fintype V] in
private theorem send_total {ι:Type} [Fintype ι] {J:Census V} (s:J.Mode) (f:ι→ℂ) :
    Poly.send s (∑i,f i)=∑i,Poly.send s (f i):=by
  ext m
  simp only [Poly.part_send,Poly.part_sum]
  by_cases h:m=s <;> simp [h]

theorem full (N p k:ℕ) (o:V→Site (R.family.side k p)) (σ:ℝ) (v:(j:V)→R.family.label (d j))
    (t:V→T→ℂ) (pos:∀j,0<d j) (h:k≤N) (x:T) (U:Config G (R.family.side k p)) :
    let g:=Pert.Asymptotics.regulatorRun R.family N p k
    let a:=R.family.path.rep N p k
    let X:=WilsonOriginalStarGradedScene.words R d o σ g a.p.threshold v t pos
    WilsonRootedKioskOccupiedSlip.bare (rendered X a.p g) x U =
      ∑j:V,Poly.send ((Stock.census V).fire j) (t j x * kernel R N p k (d j) (v j) (o j) U) := by
  intro g a X
  rw [WilsonRootedKioskOccupiedSlip.bare,tsum_fintype,Fintype.sum_sum_type,Fintype.sum_sigma,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let rows₀:=rows R d o σ g a.p.threshold v t
  change Poly.send ((Stock.census V).fire j) ((rows₀ (.inl j)).nominal g x U)+
    ∑s:WilsonOriginalStarLaurentWallet.Socket R (d j),Poly.send ((Stock.census V).fire j)
      ((rows₀ (.inr ⟨j,s⟩)).nominal g x U) = _
  rw [←send_total,←Extra.Trajectories.send_add]
  have high:(∑s:WilsonOriginalStarLaurentWallet.Socket R (d j),(rows₀ (.inr ⟨j,s⟩)).nominal g x U)=
      t j x * kernel R N p k (d j) ((R.family.labels.level (d j)).core (v j)) (o j) U :=
    monomials R d σ v t N p k h o j x U
  rw [show (rows₀ (.inl j)).nominal g x U=t j x*v j 0 from scalar_read R d o σ g a.p.threshold v t j x U,high,←mul_add]
  congr 2
  exact (WardBin.write_unitpart (R.family.localSection (d j)) (R.makes.sections (d j)) a.p.threshold
    (v j) (expandAt (o j) U)).symm

theorem birth (N p:ℕ) (o:V→Site (R.family.side N p)) (σ:ℝ) (w:(j:V)→R.family.book.Ref (d j))
    (t:V→T→ℂ) (pos:∀j,0<d j) (refs:∀j,R.family.ref (d j)≤N) (x:T) (U:Config G (R.family.side N p)) :
    let g:=Pert.Asymptotics.regulatorRun R.family N p N
    let a:=R.family.path.rep N p N
    let v:=fun j=>Price.awake R.family (d j) N N p (w j)
    let X:=WilsonOriginalStarGradedScene.words R d o σ g a.p.threshold v t pos
    let L:=rendered X a.p g
    L.log x U+(WilsonRootedKioskOccupiedSlip.sheet L.shade).log x U =
      ∑j:V,Poly.send ((Stock.census V).fire j) (t j x * R.family.O N p (w j) (o j) U) := by
  intro g a v X L
  rw [←WilsonOriginalBareMarkedSheet.restore]
  have all:=full R d N p N o σ v t pos le_rfl x U
  rw [all]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [v]
  rw [WilsonPositionThermometerStationBirth.kernel R N p (d j) (refs j) (w j) (o j)]

end YM.Integration.WilsonOriginalBarePhysicalLog
