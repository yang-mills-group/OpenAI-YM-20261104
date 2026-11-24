import YM.Integration.WilsonOriginalAlternativeGuard
import YM.Integration.WilsonOriginalAlternativeGallery

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeHosted
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal Push.Corrected Push.AbsoluteSums
open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeExtraction
open PhysicalNext.Repeat.Legato Extra.Histories
open scoped Classical BigOperators

private def move {G:Gauge} {n:Side} {V I T:Type} [DecidableEq V]
    {p b:BudgetPoint} {o:V→Site n} {J:Census V} (eq:p=b) (L:Lamps T I G p o J) :
    Lamps T I G b o J :=eq ▸ L

private theorem rec_log {G:Gauge} {n:Side} {V I T:Type} [DecidableEq V] [Fintype V]
    {p b:BudgetPoint} {o:V→Site n} {J:Census V} (eq:p=b) (L:Lamps T I G p o J)
    (x:T)(U:Config G n) : (eq ▸ L:Lamps T I G b o J).log x U=L.log x U:=by subst b;rfl

private theorem rec_paid {G:Gauge} {n:Side} {V I T:Type} [DecidableEq V]
    {p b:BudgetPoint} {o:V→Site n} {J:Census V} (eq:p=b) (L:Lamps T I G p o J) {w:V→ℝ}
    {a c:ℝ} (h:L.Paid w p.B a c) : (eq ▸ L:Lamps T I G b o J).Paid w b.B a c:=by subst b;exact h

variable {G:Gauge} (R:Run G) (N per k:ℕ) (upper:k≤N)
variable {V T I:Type} [DecidableEq V] [Fintype V] (J:Census V)
variable (o:V→Site (R.family.side k per)) (d:V→ℕ) (ref:∀i,R.family.ref (d i)≤k)
variable (v:∀i,R.family.label (d i)) (t:T→V→ℂ) (W:RG.Rep G (R.family.side k per))
variable (same : (R.family.path.rep N per k).p = W.p)
local notation "rows" => WilsonOriginalAlternativeGuard.submitted R N per k upper J o d ref v t
local notation "cost" => WilsonOriginalAlternativeGuard.rent R N per k J o d v
local notation "guard" => WilsonOriginalAlternativeGuard.value R N per k o d v t

omit [DecidableEq V] [Fintype V] in
include same in
theorem primary (x:T) (U:Config G (R.family.side k per)) (i:V) :
    guard x U i=t x i * Extra.Histories.part (R.family.localSection (d i)) (o i) W U (v i) := by
  let F:=R.family.labels.level (d i)
  let S:=R.family.localSection (d i)
  let read:=fun b:BudgetPoint=> t x i*((v i) 0+masked b.threshold (S.footprint (o i))
    (S.places (F.scaled b.threshold⁻¹ (F.core (v i))) (o i)) U)
  exact congrArg read same

def slate : Lamps T (WilsonOriginalAlternativeGuard.Tag V × Bool) G W.p (o∘Prod.fst) (board J) := move same (WilsonOriginalAlternativeGuard.submitted R N per k upper J o d ref v t)

theorem price (w:V→ℝ) (wp:∀i,0<w i) (a:ℝ) (ht:∀x i,‖t x i‖≤1) :
    (slate R N per k upper J o d ref v t W same).Paid (wallet J w) W.p.B a (cost w a) :=
  rec_paid same rows (WilsonOriginalAlternativeGuard.price R N per k upper J o d ref v t w wp a ht)

theorem field (x:T) (U:Config G (R.family.side k per)) :
    (slate R N per k upper J o d ref v t W same).log x U=ink J (guard x U) :=
  (rec_log same rows x U).trans (WilsonOriginalAlternativeGuard.field R N per k upper J o d ref v t x U)

end YM.Integration.WilsonOriginalAlternativeHosted
