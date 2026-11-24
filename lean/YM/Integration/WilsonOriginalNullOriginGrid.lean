import YM.Integration.WilsonOriginalNullPlacedFanField
import YM.Integration.WilsonOriginalNullPlacedFullMatrix
import YM.Integration.WilsonOriginalNullPlacedOffset
import YM.Integration.WilsonOriginalNullOriginCylinder

/-! Aligned descendants of a fixed grid site carry the same raw centered
Wilson section. A finite lower corridor still uses its actual child digits. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullOriginGrid
open Function Filter Lattice RG Wilson Source Labels MeasureTheory Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof
open Copper Next.Foundations Graces Roost Org Push.Local
open WilsonOriginalNullPlacedGermMap WilsonOriginalNullPlacedFullMatrix
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d N p:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

theorem public_grid {j:ℕ} (upper:j ≤ N):
    ∀ (_:(C₀).ref d ≤ j) (y:Site ((C₀).side j p)) (b:(C₀).label d),
      dyes C₀ j N p upper (((C₀).S.a j:ℂ)^d •
        (C₀).O N p (((C₀).factory d N p).terminal b) (((C₀).S.toDepth upper p).embed y))=
          calValues (C:=C₀) d N p j b ∘ Lattice.translate y := by
  induction upper using Nat.decreasingInduction with
  | self=>
    intro age y b
    rw [like_embed, dyes, MergeProof.Accent.gust_base]
    let P:=(C₀).path.rep N p N
    funext U
    change (P.eval U:ℂ)*(((C₀).S.a N:ℂ)^d*(C₀).O N p (((C₀).factory d N p).terminal b) y U)=
      (((C₀).factory d N p).entries N b).density 0 S₀ P (Lattice.translate y U)
    have born:(((C₀).factory d N p).entries N b).density 0 S₀ P (Lattice.translate y U)=
        ((C₀).S.a N:ℂ)^d*(P.eval (Lattice.translate y U):ℂ)*initial S₀ (C₀).path N p b 0 (Lattice.translate y U):=
      (R.makes.calibrated d N p age).encode b _
    rw [born]
    have shift: (C₀).O N p (((C₀).factory d N p).terminal b) y U=
        initial S₀ (C₀).path N p b 0 (Lattice.translate y U):=by
      have h:=((C₀).translation 0 y (((C₀).factory d N p).terminal b) U).symm
      simpa [Family.O,TransferData.cylinder] using h
    have invariant:=vac_pull (C₀).path N p N R.makes.wilson (le_refl N) 1 y U
    rw [Lattice.pull_one] at invariant
    change ((P.eval (Lattice.translate y U):ℝ):ℂ)=(P.eval U:ℂ) at invariant
    rw [shift,invariant];ring
  | of_succ j live ih=>
    intro age y b
    let r:=((C₀).path.levels.clock.op j p).ratio
    let Ω:=(C₀).S.toDepth live p
    let upper:=(C₀).S.toDepth live.le p
    have emb:upper.embed y=Ω.embed (r.embed y):=Next.Rank.Station.embed_comp r Ω upper y
    have moved:=WilsonOriginalNullMovedOperator.commute C₀ d N p j y (calValues (C:=C₀) d N p (j+1) b)
      (message d N p (j+1) R.makes (age.trans (Nat.le_succ j)) live (entryOk d N p (j+1) R.makes (age.trans (Nat.le_succ j)) live b))
    calc
      _=transition (C:=C₀) d N p j (dyes C₀ (j+1) N p live (((C₀).S.a (j+1):ℂ)^d •
          (C₀).O N p (((C₀).factory d N p).terminal b) (upper.embed y))):=
        (WilsonOriginalNullPlacedFanField.push R d N p j live _).symm
      _=transition (C:=C₀) d N p j (calValues (C:=C₀) d N p (j+1) b ∘ Lattice.translate (r.embed y)):=by
        rw [emb];exact congrArg _ (ih (age.trans (Nat.le_succ j)) (r.embed y) b)
      _=_:=moved.trans (congrArg (fun f=>f ∘ Lattice.translate y) (factory_eq (C:=C₀) d N p j R.makes age live b).symm)

theorem aligned {m:ℕ} (age:(C₀).ref d ≤ m) (y:Site ((C₀).side m p)) (b:(C₀).label d) (n:ℕ) (live:m+n ≤ N):
    WilsonOriginalNullPlacedFlowPanel.field R d N p m n
      (((C₀).S.toDepth (show m ≤ m+n by omega) p).embed y) b=
        calValues (C:=C₀) d N p m b ∘ Lattice.translate y := by
  induction n with
  | zero=>rw [WilsonOriginalNullPlacedFlowPanel.field,like_embed];rfl
  | succ n ih=>
    let w:=(C₀).S.toDepth (show m ≤ m+n by omega) p
    let r:=((C₀).path.levels.clock.op (m+n) p).ratio
    let v:=(C₀).S.toDepth (show m ≤ m+(n+1) by omega) p
    let field:=calValues (C:=C₀) d N p (m+n+1) b
    have emb:v.embed y=r.embed (w.embed y):=Next.Rank.Station.embed_comp w r v y
    have home:(C₀).ref d ≤ m+n:=by omega
    have step:m+n<N:=by omega
    have read:=message d N p (m+n+1) R.makes (home.trans (Nat.le_succ _)) step
      (entryOk d N p (m+n+1) R.makes (home.trans (Nat.le_succ _)) step b)
    change flow C₀ d N p m n (transition (C:=C₀) d N p (m+n) (field ∘ Lattice.translate (v.embed y)))=_
    rw [emb,WilsonOriginalNullMovedOperator.commute C₀ d N p (m+n) (w.embed y) field read]
    change flow C₀ d N p m n
      (transition (C:=C₀) d N p (m+n) (calValues (C:=C₀) d N p (m+n+1) b) ∘ Lattice.translate (w.embed y))=_
    rw [←factory_eq (C:=C₀) d N p (m+n) R.makes home step b]
    exact ih step.le

end YM.Integration.WilsonOriginalNullOriginGrid
