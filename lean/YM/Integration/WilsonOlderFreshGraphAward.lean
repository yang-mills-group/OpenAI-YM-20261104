import YM.Integration.WilsonOlderFreshGraphPublication
import YM.Integration.WilsonOlderFreshGraphMount

/-! Co-issue the planted column on the physical school. Its comparison
premise reads only the original, signed, folded polynomial of the normalized
section, jointly with the auxiliary soft links. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphAward
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

def probe (i:ℕ) (w:Letter (R.family.labels.level d)) (p:Ballot i D)
    (n:Side)(s:Board Unit n ℝ)(j:ℕ)(A:Board (Loc G 1) n ℝ):ℝ:=
  ∑y:Site n,s (y,())*MvPolynomial.eval (fun x:wire G n=>A (y+x.1,x.2))
     (coeff j (Kemp.banner d (Primer.fieldCoeffs R.family a L depth p.1.1 i w p.2) n))

theorem original {φ U:ℕ→ℕ} (law:VowsR.LawScroll G φ)
    (I:Unit→Loan) (toll:d≤(I ()).toll) (Q:ℕ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G I d Q) simple law)
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)):
    let M:=menu G I d Q
    let H:=roots M simple R.metals.p R.metals.K
    (∃ B,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) B) ∧
    ∀ᶠ i:ℕ in atTop,
      (∀(n:Side)(s:Board Unit n ℝ)(j:ℕ),j≤Q→∀p:Ballot i D,
        Haiku.Vernal G n (probe R L a depth i w p n s) j) →
      ∃ P:ℕ→Ballot i D→Poetry.Roll G Unit,
       (∀(k:ℕ),1≤k→∀j≤Q,Agenda.Booked {()} () I (P j) (test i D) j
          (2*Agenda.seed H φ k (R.family.path.levels.clock.J i)) 1) ∧
       (∀j≤Q,∀(p:Ballot i D)(n:Side)(A:Board (Loc G 1) n ℝ)(s:Board Unit n ℝ),
         probe R L a depth i w p n s j A =
           ∑l∈Finset.range (Q+1),((P l p).folded l j).table n (mingle A s)) := by
  intro M H
  have school:=WilsonOlderFreshGraphSchool.on_run M simple law R purchase.1
  refine ⟨school.1,?_⟩
  filter_upwards [WilsonOlderFreshGraphPainter.original R L a depth simple purchase.2 o w I toll Q,
    WilsonOlderFreshGraphPublication.original R L a depth simple purchase.2 o w] with i painter native
  intro vernal
  have folded (p:Ballot i D)(n:Side)(s:Board Unit n ℝ):
      (fun j A=>(sheet R L a depth i w j p).table n (mingle A s)) =
        probe R L a depth i w p n s:=funext fun j=>funext fun A=>native p.1.1 p.1.2 p.2 j n A s
  obtain ⟨P,receipt⟩:=painter (fun n s j hj p=>folded p n s ▸ vernal n s j hj p)
  refine ⟨P,?_,fun j hj p n A s=>(congrFun (congrFun (folded p n s).symm j) A).trans
    (receipt.recollects j (Nat.lt_succ_of_le hj) p n A s)⟩
  intro k hk j hj
  have h:=school.2 k (R.family.path.levels.clock.J i) hk
  have idK:R.family.path.levels.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
  apply Agenda.booked_turn {()} () I _ (receipt.booking j (Nat.lt_succ_of_le hj))
  change 2*Agenda.seed H φ k _≤Agenda.path (width G R.family.path.levels.clock.kernel d Q _) I {()} Q (Q+1)
  rw [idK]
  change Agenda.seed H φ k _≤Agenda.path (width G R.metals.p.kernel d Q _) I {()} Q (Q+1)/(16*1) at h
  have pos:=Agenda.stem H φ k (R.family.path.levels.clock.J i)
  linarith

end YM.Integration.WilsonOlderFreshGraphAward
end
