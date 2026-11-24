import YM.FormalOPE.RG10.OpenSlots.Settlement
/-!
 # Full-field kernel recursion and its coherence with the bare diagram

 This defines an OFF-truss formal evolution: even-orbit fields in the native full link
 variables, Hessian etc computed before choosing any subsequent truss. Thus it can be
 studied in norms using all coarse field variables. We project it here and prove that
 arbitrary fixed interior tree choices and finite numbers of steps give the correct
 orbit-regulated *integrated* coefficient; this is an exact alternative algorithm to
 evaluating that prescription. No assertion that Ward identities in the fully opened
 algebra for these off-truss polynomials have been supplied.Splice.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.OpenSlots
open MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof Router Quadratic
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {J:ChartRatio G}
 def Commission (J:ChartRatio G){n:Side}{L:Fabric G n}(T:Cloth L)(U:Unmasked G n)(z:L.Cost→PowerSeries ℝ) : Prop:= match T with
 | .floor _ _ _=> (drag (castAt T) U.Q).RespectsPrice
 | .inLayer (t:=t) P C => ∃ h:(core (gated P U t (z none))).RespectsPrice, Commission J C (Update P t J (z none) U h) (z∘some)
lemma resident {n:Side}{he:_root_.Even n.val}{T: (Fabric.endcap (G:=G) n he).loom.Truss} {U:Unmasked G n}{L:Law (Field (Cloth.floor n he T).choose)}{W:Ticket (Field (Cloth.floor n he T).choose)}{z}(h:Bank (Cloth.floor n he T) J z U L W): (drag (castAt (Cloth.floor n he T)) U.Q).P=L.P:= records _ (recordQ L) (fun x=> (show L.P x x= U.Q.flourish _ from by rw [h.main,done z,add_zero]).symm)
lemma released (H:LocalRatio J){n:Side}{L:Fabric G n}{T:Cloth L} {U:Unmasked G n}{Λ: Law (Field T.choose)}{W:Ticket (Field T.choose)}{z:L.Cost→PowerSeries ℝ}(h:Bank T J z U Λ W): Commission J T U z:= by
 cases T with
 | floor=> exact (show (drag _ U.Q).RespectsPrice from ⟨Λ,resident h⟩)
 | inLayer P C=> rw [Commission]; exact ⟨h.respects, released H (h.confirmation H)⟩
termination_by structural T
 def course {n:Side}{L:Fabric G n}(T: Cloth L)(z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(J:ChartRatio G) (A:Ticket (Flats G n)) (h:Commission J T U z): PowerSeries ℝ:= match T with
 | .floor k b Y=> let T0:= Cloth.floor k b Y;
                   enjoy (show Law (Field T0.choose) from (show (drag _ U.Q).RespectsPrice from h).inner) (tangent G T0.choose.Bulk) (boost (castAt T0) A) (boost (castAt T0) U.W * tissue J T0.choose.Bulk)
 | .inLayer (t:=t) P C=>
   let r:(core (gated P U t (z none))).RespectsPrice:= Exists.choose h
   course C (z∘some) (Update P t J (z none) U r) J (Broadcast P t J (z none) U r (boost (blankRight P) A)) (Exists.choose_spec h)

lemma earns (H:LocalRatio J){n:Side}{L:Fabric G n}{T:Cloth L} {U:Unmasked G n}{Λ: Law (Field T.choose)}{W:Ticket (Field T.choose)}{z:L.Cost→PowerSeries ℝ}(A:Ticket (Flats G n))(h: Bank T J z U Λ W)(u:incline U.W): course T z U J A (released H h)= transaction T Λ (boost (castAt T) A) W:= by
 cases T with
 | floor k b Y=>
   let T:=Cloth.floor n b Y
   let P:= (show (drag _ U.Q).RespectsPrice from (released H h) : (drag (castAt T) U.Q).RespectsPrice)
   have hf: P.inner=Λ:= P.pinpoints (resident h)
   have hw:W= boost (castAt T) U.W * tissue J _:= by rw [h.price,off z,mul_one]
   rw [course,transaction]; change enjoy P.inner (tangent G T.choose.Bulk) _ _= _; rw [hf,←hw]
 | @inLayer c f S H₀ t hf L P C=>
   rw [course]; let D:= Pathway (H:=H₀) (t:=t) (hf:=hf) (P:=P) (C:=C)
   conv_rhs=> rw [transaction,←Bank.x_pull]
   let A':= Broadcast P t J (z none) U h.respects (boost (blankRight P) A)
   let μ':= tangent G (Index S P)
   have he:= h.imprint H u (boost (blankRight P) A)
   change _= transaction C (rest Λ D) (delivered Λ D μ' _ W) (reclose Λ D μ' W); rw [he]; exact earns H A' (h.confirmation H) (funded H (z none) u h.respects)
termination_by structural T
end YM.FormalOPE.RG10.OpenSlots
