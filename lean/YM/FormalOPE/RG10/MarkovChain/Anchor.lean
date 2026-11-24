import YM.FormalOPE.RG10.MarkovChain.Traverse
/-!
 # Genuine Weight timetable at every finite truss
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {L:Fabric G n}{T:Cloth L}
namespace Library
variable {u v:Ticket (Field T.choose)}
lemma additive (h:Library T u)(hk:Library T v):Library T (u+v):= by intro i; rw [map_add]; exact Roof.add (h i) (hk i)
lemma empty : Library T 0:= fun i=>by rw [map_zero]; exact Roof.neutral T
lemma finSum {α:Type}(V:α→ Ticket (Field T.choose))(s:Finset α)(h:∀ i∈s,Library T (V i)): Library T (∑ i∈s,V i):= by
 induction s using Finset.induction with
 | empty=> rw [Finset.sum_empty]; exact empty
 | insert i s hq ih=> rw [Finset.sum_insert hq]; exact additive (h i (by simp)) (ih (fun i hi=> h i (by simp [hi])))
lemma receipt (p:PowerSeries ℝ)(h:Library T u): Library T (carry p * u):= by
 intro i
 have he :(coeff i (carry (E:=Field T.choose) p * u)).val=∑ j∈ Finset.antidiagonal i, coeff j.1 p • (coeff j.2 u).val:= funext fun x=> by simp [←reading_term, coeff_mul, Finset.sum_apply]
 rw [he]
 exact Roof.billSum _ _ (fun j _=> Roof.smul (h j.2) (coeff j.1 p))

variable (w:L.Accounts→PowerSeries ℝ)(hw:∀ i,0<term (w i) 0)
-- x assignment. notation Y
local notation "Y"=> model L T.choose w
local notation "B"=> Direction G T.choose.Bulk
include hw
lemma halo : Library T (dressing Y) := by
 unfold dressing; refine finSum _ _ (fun i _=> Library.receipt _ ?_)
 intro k; unfold spikeCost drop imbed rise; rw [coeff_mk,coeff_mk]; exact Roof.differentiated ((enough L T.choose w hw).localAll i).germ (vacuum T i) _
lemma ascends : Library T (advancing ((Y).target ∘ expLinks G T.choose.Bulk)):= by
 intro i
 let a:= (Y).target ∘ expLinks G T.choose.Bulk; by_cases h:i=0
 · subst i; rw [coeff_zero_eq_constantCoeff_apply, advancing_zero]; exact Roof.neutral T
 change Roof T (coeff i (advancing a)).val
 rw [show (coeff i (advancing a)).val=(-1:ℝ) • (jet a (2+i)) from funext fun x=> by
      rw [←reading_term,levels]; simp [Radial.layers,h,Nat.add_comm 2]]
 exact Roof.smul (Roof.differentiated ((enough L T.choose w hw).entire.smooth.of_le le_top) (show Roof T a from Roof.habituate (T:=T) _) _) _
lemma weightSaved {P:ChartRatio G}(J:LocalRatio P) : Vault T (weight P Y):= by
 unfold weight; refine Vault.mul ?_ (Vault.mul (Vault.mul (Vault.charge J) (Vault.expForm (ascends w hw) (advancing_zero _))) (Vault.expForm (halo w hw) (dressing_zero _ (enough L T.choose w hw))))
 rw [show ∀ x:ℝ, roll (E:= B) x=carry (C x) from fun x=> (PowerSeries.map_C ..).symm]; exact Vault.fromFixed _ -- B notation interferes
end Library
end YM.FormalOPE.RG10.MarkovChain
