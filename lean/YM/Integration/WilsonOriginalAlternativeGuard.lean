import YM.Integration.WilsonOriginalAlternativeExtraction
import YM.Integration.WilsonOriginalAlternativeMenu
import YM.Integration.WilsonOriginalStarPrimaryCatalog

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeGuard
open Function Finset Lattice Wilson RG Marker QuadraticLocal Push.Corrected Push.AbsoluteSums
open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeExtraction
open PhysicalNext.Repeat.Legato
open Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p k:ℕ) (upper:k≤N)
variable {V T:Type} [DecidableEq V] [Fintype V] (J:Census V)
variable (o:V→Site (R.family.side k p)) (d:V→ℕ) (ref:∀i,R.family.ref (d i)≤k)
variable (v:∀i,R.family.label (d i)) (t:T→V→ℂ)
local notation "P_" => R.family.path.rep N p k
abbrev Tag (V:Type) := {j:V×Port // j.2≠0}

def rows (i:Tag V) : Lamps T Bool G (P_).p (o∘Prod.fst) (board J) :=
  WilsonOriginalStarPrimaryCatalog.catalogue R N p k (d i.val.1) upper (ref _) _ i.val (v _)
    (fun x=>entry (t x) i.val)

def submitted : Lamps T (Tag V×Bool) G (P_).p (o∘Prod.fst) (board J) :=
  WilsonOriginalAlternativeMenu.pool (rows R N p k upper J o d ref v t)

def rent (w:V→ℝ) (a:ℝ) : ℝ:=∑i:Tag V,
  WilsonOriginalStarPrimaryCatalog.rent R N p k (d i.val.1) (o∘Prod.fst) i.val (v _)
    (wallet J w) a

theorem price (w:V→ℝ) (wp:∀i,0<w i) (a:ℝ) (ht:∀x i,‖t x i‖≤1) :
    (submitted R N p k upper J o d ref v t).Paid (wallet J w) (P_).p.B a
      (rent R N p k J o d v w a) := by
  apply WilsonOriginalAlternativeMenu.price
  intro i
  apply WilsonOriginalStarPrimaryCatalog.funded _ _ _ _ _ _ _ _ _ _ _ _ (positive J wp)
  intro x
  by_cases one:i.val.2=1 <;> simp [entry,i.prop,one,ht]

def value (x:T) (U:Config G (R.family.side k p)) (i:V) : ℂ:=
  t x i * WilsonOriginalStarPrimaryCatalog.primary R N p k (d i) o i (v i) U

theorem field (x:T) (U:Config G (R.family.side k p)) :
    (submitted R N p k upper J o d ref v t).log x U=ink J (value R N p k o d v t x U) := by
  classical
  let g:=fun i:V×Port=>Poly.send ((board J).fire i) (entry (value R N p k o d v t x U) i)
  have all:(∑i:Tag V,g i.val)=∑i:V×Port,g i:=by
    have keep:(∑'i:Tag V,g i.val)=∑'i:V×Port,g i:=by
      apply Subtype.val_injective.tsum_eq
      intro i live
      by_cases dead:i.2=0
      · exact False.elim (live (by simp [g,entry,dead]))
      · exact ⟨⟨i,dead⟩,rfl⟩
    simpa only [tsum_fintype] using keep
  rw [submitted,WilsonOriginalAlternativeMenu.original]
  change _=∑ i:V×Port,g i
  rw [← all]
  apply Finset.sum_congr rfl
  intro i _
  let L:=rows R N p k upper J o d ref v t i
  have own:∀z,L.mode z=(board J).fire i.val:=fun _=>rfl
  rw [WilsonOriginalAlternativeMenu.mono _ L own]
  unfold L rows
  rw [WilsonOriginalStarPrimaryCatalog.filed]
  dsimp only [g,value]
  by_cases y:i.val.2=1
  · simp only [entry,if_neg i.prop,if_pos y];rfl
  · simp only [entry,if_neg i.prop,if_neg y,neg_mul];rfl

end YM.Integration.WilsonOriginalAlternativeGuard
