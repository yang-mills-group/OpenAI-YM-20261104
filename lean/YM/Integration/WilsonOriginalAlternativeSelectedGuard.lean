import YM.Integration.WilsonOriginalAlternativeHosted
import YM.Integration.WilsonOriginalAlternativeRetest

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeSelectedGuard
open Function Finset Set Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N p k:ℕ) (upper:k ≤ N)
variable {V:Type} [DecidableEq V] [Fintype V] (J:Census V) (o:V→Site (R.family.side k p))
  (d:V→ℕ) (ref:∀i,R.family.ref (d i) ≤ k) (v:∀i,R.family.label (d i)) (c:V→Port)
local notation "D_" => (WilsonOriginalAlternativeFiniteSource.disks (V:=V))
local notation "K_" => (WilsonOriginalAlternativeFiniteSource.sectors (V:=V))
local notation "P_" => R.family.path.rep N p k
def sign (tag:Port):ℂ:=if tag=0 then 0 else if tag=1 then 1 else -1
def rate (t:Wallet D_)(j:V):ℂ:=sign (c j)*(t j).val
def lamp (j:V):Lamps (Wallet D_) Bool G (P_).p o J:=
  WilsonOriginalStarPrimaryCatalog.catalogue R N p k (d j) upper (ref j) o j (v j) (fun t=>rate c t j)
def port:=WilsonOriginalAlternativeMenu.pool (lamp R N p k upper J o d ref v c)
def rent (w:V→ℝ) (a:ℝ):ℝ:=∑j,WilsonOriginalStarPrimaryCatalog.rent R N p k (d j) o j (v j) w a

theorem paid (w:V→ℝ) (wp:∀i,0<w i) (a:ℝ):
    (port R N p k upper J o d ref v c).Paid w (P_).p.B a (rent R N p k o d v w a):=by
  apply WilsonOriginalAlternativeMenu.price
  intro j
  apply WilsonOriginalStarPrimaryCatalog.funded _ _ _ _ _ _ _ _ _ _ _ _ wp
  intro x
  rw [rate,norm_mul]
  apply mul_le_one₀ _ (norm_nonneg _) (x j).property
  unfold sign
  split_ifs <;> simp

omit [Fintype V] in
theorem tests (X:V→Support (R.family.side k p)) (anchored:∀i,X i⊆(R.family.localSection (d i)).footprint (o i)):
    Taut X D_ K_ (port R N p k upper J o d ref v c):=by
  constructor
  · intro ix j hj;have same:j=ix.1:=Finset.mem_singleton.mp hj
    subst j;exact anchored _
  · rintro ⟨i,b⟩ U
    have h:=WilsonOriginalAlternativeFiniteSource.attentive (V:=V) i
    have amp:Attn K_ D_ {i} (fun t=>rate c t i):=by
      simpa only [rate,WilsonOriginalAlternativeFiniteSource.probe,mul_comm (sign (c i))] using h.sc (sign (c i))
    cases b
    · exact amp.sc _
    · exact amp.sc _

theorem total (x:Wallet D_) (U:Config G (R.family.side k p)):
    (port R N p k upper J o d ref v c).log x U=
      ∑j,Poly.send (J.fire j) (rate c x j*WilsonOriginalStarPrimaryCatalog.primary R N p k (d j) o j (v j) U):=by
  rw [port,WilsonOriginalAlternativeMenu.original]
  apply Finset.sum_congr rfl
  intro i _
  let L:=lamp R N p k upper J o d ref v c i
  have its:∀j,L.mode j=J.fire i:=fun _=>rfl
  rw [WilsonOriginalAlternativeMenu.mono i L its]
  congr 1
  exact WilsonOriginalStarPrimaryCatalog.filed .. 

end YM.Integration.WilsonOriginalAlternativeSelectedGuard
