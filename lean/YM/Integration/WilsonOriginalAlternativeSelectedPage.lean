import YM.Integration.WilsonOriginalAlternativeSelectedGuard

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeSelectedPage
open Function Finset Set Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction WilsonOriginalAlternativeSelectedGuard
open scoped Classical BigOperators
private def castLamps {G:Gauge} {n:Side} {V I T:Type} [DecidableEq V]
    {a b:BudgetPoint} {o:V→Site n} {J:Census V} (same:a=b) (L:Lamps T I G a o J):
    Lamps T I G b o J:=same ▸ L

variable {G:Gauge} (R:Run G) (N p k:ℕ) (upper:k ≤ N)
variable {V:Type} [DecidableEq V] [Fintype V] (J:Census V) (o:V→Site (R.family.side k p))
  (d:V→ℕ) (ref:∀i,R.family.ref (d i) ≤ k) (v:∀i,R.family.label (d i)) (c:V→Port)
local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "K_" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
local notation "P_" => R.family.path.rep N p k
variable (b:BudgetPoint) (same:(R.family.path.rep N p k).p=b)
def paper:Lamps (Wallet D_) (V×Bool) G b o J:= castLamps same (port R N p k upper J o d ref v c)
local notation "L_" => paper R N p k upper J o d ref v c b same

theorem price (w:V→ℝ) (wp:∀i,0<w i) (a:ℝ):
    (L_).Paid w b.B a (rent R N p k o d v w a):=by
  subst b
  exact paid R N p k upper J o d ref v c w wp a

omit [Fintype V] in
theorem lawful (X:V→Support (R.family.side k p)) (anchored:∀i,X i⊆(R.family.localSection (d i)).footprint (o i)):
    Taut X D_ K_ (L_):=by
  subst b
  exact tests R N p k upper J o d ref v c X anchored

theorem printed (x:Wallet D_) (U:Config G (R.family.side k p)):
    Poly.pass ((L_).log x U) = word J (fun j=>entry
      (fun i=>(x i).val*WilsonOriginalStarPrimaryCatalog.primary R N p k (d i) o i (v i) U) (j,c j)):=by
  subst b
  change Poly.pass ((port R N p k upper J o d ref v c).log x U)=_
  rw [total]
  ext s
  rw [Extra.Trajectories.pass_fire]
  apply Finset.prod_congr rfl
  intro j _
  simp only [rate,sign,entry]
  split_ifs <;> ring

end YM.Integration.WilsonOriginalAlternativeSelectedPage
