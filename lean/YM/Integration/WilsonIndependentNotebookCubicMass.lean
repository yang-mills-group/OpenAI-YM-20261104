import YM.Integration.WilsonIndependentNotebookCubicReports
import YM.Integration.WilsonIndependentMatchedRosterChronology

/-! Match the native right-associated first-join roster to the AB deposit on
the actual Wilson stencils, using their finite fields and covered lifts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookCubicMass
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power
open Embroider Precision Exterior Fountain Soil Gauge Source Source.Drops Labels WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Classical
variable {G:Gauge}

private theorem full {i j:ℕ}{X Y:Era G ℝ}(hx:Auth i X)(hy:Auth j Y)(boards:∀n,X.1 n=Y.1 n):X=Y:=by
  have h:X.1=Y.1:=funext boards
  refine Prod.ext h ?_
  funext e r
  apply Bends.exten (hx.wing e r)
  rw [h]
  exact hy.wing e r

theorem assoc {i j k:ℕ}{X Y Z:Era G ℝ}(x:Auth i X)(y:Auth j Y)(z:Auth k Z):
    agateV (agateV X Y) Z=agateV X (agateV Y Z):=by
  apply full ((x.manor y).manor z) (x.manor (y.manor z))
  intro c
  let P:=X.1 c;let Q:=Y.1 c;let R:=Z.1 c
  have p:=x.span c;have q:=y.span c;have r:=z.span c
  have ab:=woad_shell P Q p q;have bc:=woad_shell Q R q r
  change woad (woad P Q) R=woad P (woad Q R)
  apply by_flash (woad_shell _ _ ab r) (woad_shell _ _ p bc) (woad_pure (woad P Q) R) (woad_pure P (woad Q R))
  rw [woadap _ _ (finite_shell ab) (finite_shell r),woadap _ _ (finite_shell p) (finite_shell bc),
    woadap _ _ (finite_shell p) (finite_shell q),woadap _ _ (finite_shell q) (finite_shell r),mul_assoc]

theorem roster (P:Fin 3→Era G ℝ)(l:Fin 3→ℕ)(paid:∀a,Auth (l a) (P a)):
    MassP G ℝ 2 P=agateV (agateV (P 0) (P 1)) (P 2):=
  (assoc (paid 0) (paid 1) (paid 2)).symm

/-- The actual income for a native three-slot gap applies to all four
cubic deposits together on their true held fields. -/
theorem born (A:Levels G){Ñ:ChartRatio G}{m N:ℕ}(simple:G.Simple)(ratio:LocalRatio Ñ)
    (edge:m<N)(P:Fin 3→Era G ℝ)(l:Fin 3→ℕ)(paid:∀a,Auth (l a) (P a)):
    DeltaGap A Ñ m N P l=(WilsonIndependentNotebookCubicField.issue A Ñ m N
       (l 0) (l 1) (l 2) (P 0) (P 1) (P 2)).birth:=by
  let X:=fun a=>verseI A Ñ m N (l a) (P a)
  have actual:∀a,Auth (l a) (X a):=fun a=>Auth.verse A edge simple ratio (paid a)
  have count:(∑a,l a)=l 0+l 1+l 2:=by simp [Fin.sum_univ_succ,Nat.add_assoc]
  change verseI A Ñ m N (∑a,l a) (MassP G ℝ 2 P)-MassP G ℝ 2 X=_
  rw [roster P l paid,roster X l actual,count,WilsonIndependentNotebookCubicField.parts]
  let Z:=WilsonIndependentNotebookCubicField.issue A Ñ m N (l 0) (l 1) (l 2) (P 0) (P 1) (P 2)
  change Z.proper+Z.birth-Z.proper=Z.birth
  abel

/-- Apply the full conditioned roster wage at the older stop to the
separately issued numerical cubic notebook. The last birth is the given
signed change on exactly the temporary old and fitted upper stencils. -/
theorem original (A:Levels G){Ñ:ChartRatio G}{m N n:ℕ}(simple:G.Simple)(ratio:LocalRatio Ñ)(span:m+n ≤ N)
    (P:Fin 3→Era G ℝ)(l:Fin 3→ℕ)(paid:∀a,Auth (l a) (P a))
    {U V:Era G ℝ}(u:Auth (l 2) U)(v:Auth (l 2) V)(changed:P 2=U-V):
    cruises A Ñ N (∑a,l a) (m+n) m (MassP G ℝ 2 P)=
      WilsonIndependentNotebookCubicSeeds.bill A Ñ m N (l 0) (l 1) (l 2) n (P 0) (P 1) U V:=by
  have count:(∑a,l a)=l 0+l 1+l 2:=by simp [Fin.sum_univ_succ,Nat.add_assoc]
  rw [roster P l paid,count,changed,pairingP,cruisePlus A (Nat.le_add_right m n) simple ratio span
    (((paid 0).manor (paid 1)).manor u) (((paid 0).manor (paid 1)).manor v)]
  exact WilsonIndependentNotebookCubicSeeds.original A simple ratio span (paid 0) (paid 1) u v

end YM.Integration.WilsonIndependentNotebookCubicMass
