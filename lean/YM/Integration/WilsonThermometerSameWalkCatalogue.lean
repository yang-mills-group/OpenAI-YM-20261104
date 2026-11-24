import YM.Integration.WilsonOriginalStarPrintedRead
import YM.Integration.WilsonThermometerSameWalkTrim

/-! Filing the literal masked section on the independently reclosed Wilson host. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkCatalogue
open Function Filter Finset Lattice Wilson RG Source Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint
open QuadraticLocal.Fusion.Attached MergeProof.Accent WilsonOriginalStarIncoming
open WilsonOriginalDepositedRegular WilsonOriginalDepositedRegularWindow WilsonOriginalDepositedRegularHearing
open WilsonOriginalStarIncomingRead WilsonOriginalStarPrimaryCatalog PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology

variable {G : Gauge} {V T I L : Type} [DecidableEq V] {J:Census V}
private def transport {n:Side} {o:V→Site n} {a b:BudgetPoint} (same:a=b) (X:Lamps T I G a o J):Lamps T I G b o J:=
  same ▸ X

private theorem read {n:Side} {o:V→Site n} {a b:BudgetPoint} (same:a=b) (X:Lamps T I G a o J) (x:T) (U:Config G n):
    (transport same X).log x U=X.log x U := by subst b; rfl

private theorem paid {n:Side} {o:V→Site n} {a b:BudgetPoint} (same:a=b) (X:Lamps T I G a o J)
    (w:V→ℝ) (α z:ℝ) (bill:X.Paid w a.B α z):(transport same X).Paid w b.B α z:=by subst b;exact bill

variable (R:Run G) (N per i d:ℕ) (live:i≤N) (ref:R.family.ref d ≤ i)
  {E:Passport (R.family.side i per) V} (P:Rep G (R.family.side i per))
  (same:(R.family.path.rep N per i).p=P.p) (j:V) (v:R.family.label d) (tag:T→ℂ)
local notation "A₀" => catalogue (J:=J) R N per i d live ref E.origin j v tag

def placed : Lamps T Bool G P.p E.origin J:=transport same A₀

local notation "X₀" => placed (J:=J) R N per i d live ref (E:=E) P same j v tag

theorem funded (w:V→ℝ) (active:∀j,0<w j) (α:ℝ) (test:∀x,‖tag x‖≤1):
    (X₀).Paid w P.p.B α (rent R N per i d E.origin j v w α):=
  paid same (A₀) w α _ (WilsonOriginalStarPrimaryCatalog.funded (J:=J) R N per i d live ref E.origin j v tag w active α test)

variable [Fintype V]

theorem field (x:T) (U:Config G (R.family.side i per)):
    ((X₀).log x U).part (J.fire j)=tag x*(v 0+masked P.p.threshold ((R.family.localSection d).footprint (E.origin j))
      ((R.family.localSection d).places ((R.family.labels.level d).scaled P.p.threshold⁻¹ ((R.family.labels.level d).core v)) (E.origin j)) U):=by
  rw [placed,read,WilsonOriginalStarPrimaryCatalog.filed]
  rw [←same]
  rfl

theorem received (old:Incoming E P T I J) (M:Lamps T L G P.p E.origin J)
    (q:Coefficient (R.family.labels.level d) (R.family.side i per)) (shape:q.Format (E.origin j) R.family.params P)
    (tag:T→ℂ) (D:ℕ) (w:V→ℝ) (active:∀j,0<w j) (test:∀x,‖tag x‖≤1)
    {κ B a e h:ℝ} (wallet:q.remBound (E.origin j) P κ B) (wide:1 ≤ P.p.supportExponent)
    (p₀:M.Paid w P.p.B (P.p.supportExponent+1+1) a)
    (reg:old.old.Paid w P.p.B (P.p.supportExponent+1+1) e) (hard:old.hard.Paid w P.p.B P.p.supportExponent h)
    (x:T) (U:Config G (R.family.side i per)):
    let after:=WilsonThermometerSameWalkTrim.booked old j q shape tag D
    let source:=placed (J:=J) R N per i d live ref (E:=E) P same j q.x tag
    ((exhibit (WilsonThermometerSameWalkTrim.pointed after) (M.join source)).density x U).part (J.fire j) -
      ((exhibit (WilsonThermometerSameWalkTrim.pointed old) M).density x U).part (J.fire j) =
      tag x*(q.density (E.origin j) (R.family.localSection d) P U-(P.eval U:ℂ)*tail P q D U):=by
  intro after source
  have cost:=funded (J:=J) R N per i d live ref (E:=E) P same j q.x tag w active (P.p.supportExponent+1+1) test
  have quote:=Lamps.joinPaid p₀ cost
  have posted:=WilsonThermometerSameWalkTrim.measured old j q shape tag D w active test wallet wide M (M.join source)
    (R.family.localSection d) p₀ quote reg hard x U
  have α:0≤P.p.supportExponent+1+1:=by linarith [P.p.exponent_pos]
  rw [Lamps.joinLog x U (p₀.sums α active x U) (cost.sums α active x U),Poly.part_plus,
    field (J:=J) R N per i d live ref (E:=E) P same j q.x tag x U] at posted
  unfold WilsonOriginalStarIncomingRead.primary at posted
  linear_combination posted

end YM.Integration.WilsonThermometerSameWalkCatalogue
end
