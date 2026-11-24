import YM.Integration.WilsonThermometerPositionTunedCorrection

/-! Submit Galop's varying engineering and Wick coordinates as finite *actual*
original position marks on its own mesh. The resulting signed change tests
precisely those original group fields and the common normalized vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedPublicCharge
open Function Lattice Wilson Labels Source Source.Drops XSpace PhysicalNext.Repeat.Legato
open XSpace.Normalize XSpace.Cirrus XSpace.Rose XSpace.Structure1
open WilsonThermometerPositionTunedObserved
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (W:Initialize G) {n:ℕ} (d:ℕ) (x:Sample n)
abbrev Axis := (k:Fin (d+1)) × (R.family.labels.level k).Index
variable (p:Tags G d n) (S:Finset (Fin n))
abbrev Picked := S → Axis R d
def axisFee (i:Fin n) (a:Axis R d) : ℂ := fee R W x.F a.1 (part d a.1 (p i)) a.2
def row (i:Fin n) (a:Axis R d) : Bare.Series (W.tree x.F.p) G :=
  WilsonThermometerPositionTunedSurvey.row R W a.1 x.F.p (W.tree x.F.p) (chartV x i) a.2

def charge (a:Picked R d S) : ℂ := ∏j:S,axisFee R W d x p j.val (a j)

def loan (a:Picked R d S) : PowerSeries ℂ :=
  WilsonThermometerPositionTunedSlope.finite R (fun j:S=>(a j).1.val) x.F.p
    (fun j=>x.layout j.val) (W.tree x.F.p) (fun j=>(a j).2)

def change (a:Picked R d S) : PowerSeries ℂ :=
  WilsonThermometerPositionTunedCorrection.residual R W (fun j:S=>(a j).1.val) x.F.p
    (fun j=>x.layout j.val) (W.tree x.F.p) (fun j=>(a j).2)

theorem enrolled (i:Fin n) :
    point R W x d (chartV x i) (p i) = ∑ a:Axis R d,axisFee R W d x p i a • row R W d x i a := by
  rw [Fintype.sum_sigma]
  rfl

def submitted : PowerSeries ℂ := ∑ a:Picked R d S,charge R W d x p S a • loan R W d x S a

def signed : PowerSeries ℂ := ∑ a:Picked R d S,charge R W d x p S a • change R W d x S a

theorem ordinary :
    submitted R W d x p S - Rose.numberA W d x p S = signed R W d x p S := by
  classical
  have product : (∏ i∈S,point R W x d (chartV x i) (p i)) =
      ∑a:Picked R d S,charge R W d x p S a • (∏ i:S,row R W d x i.val (a i)) := by
    rw [← Finset.prod_coe_sort S]
    simp_rw [enrolled R W d x p, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [charge, Algebra.smul_def,Finset.prod_mul_distrib,map_prod]
  rw [WilsonThermometerPositionTunedObserved.ordinary R W x d p S,product,map_sum]
  simp only [map_smul]
  unfold submitted signed
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  change _ • loan R W d x S a - _ • Bare.normalized (W.tree x.F.p) G
    (∏ j:S,row R W d x j.val (a j)) = _ • change R W d x S a
  rw [← smul_sub]
  exact congrArg (charge R W d x p S a • ·)
    (WilsonThermometerPositionTunedCorrection.face R W (fun j:S=>(a j).1.val) x.F.p
       (fun j=>x.layout j.val) (W.tree x.F.p) (fun j=>(a j).2))

end YM.Integration.WilsonThermometerPositionTunedPublicCharge
end
