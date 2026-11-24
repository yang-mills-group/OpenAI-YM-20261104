import YM.RG05Readout.Capture.Plum

/-! Keep each original singleton and its forced key while re-enrolling the complete field between the separated date and geometric capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnchangedGrouping
open Function Filter Finset MeasureTheory Relation Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Ribbon Menu Marker Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Ribbons Ribbons.Fibers Ribbons.ManyCopies
open Ribbons.ManyCopies.Muster RG05Readout RG05Readout.Address RG05Readout.Many
open scoped Topology Classical BigOperators
set_option quotPrecheck false
variable {G:Gauge} {n:Side} {I:Type} [Fintype I] [DecidableEq I]
private def identity (I:Type)( _dec:DecidableEq I)( _finite:Fintype I): Fibers I I:=⟨id,id,fun _=>rfl⟩
local notation "L" => identity I inferInstance inferInstance
local notation "J" => Stock.census (Unit×I)
local notation "T" => partialGroup Unit (L)
private theorem content (i:Unit×I):(T).contents i={i}:=by
  ext j
  rw [Fibers.focuses,Finset.mem_singleton]
  rfl

theorem alone (B:ℕ) (x:Site n) : coverNumber B ({x}:Support n) ≤ 1:=by
  have con:Corona.Ships ({x}:Support n) (B+B+1):=by
    intro u hu v hv
    simp only [Finset.mem_singleton] at hu hv
    subst u; subst v; exact Relation.ReflTransGen.refl
  simpa only [Finset.card_singleton] using Corona.list_cost B
    (show covers B ({x}:Support n) {x} from ⟨halo_subset _ _,Corona.ship_halo B con⟩)

theorem original (R:Rep G n) (P:Unit×I→Three G n) (X:Config G n→Poly (J))
    (o:Unit×I→Site n) (w:Unit×I→ℝ) {t η z y:ℝ} {M:ℕ}
    (cap:Alcove R P X o w t η (1/2)) (stock:Arsenal R) (valid:R.activities.Valid R.p z y)
    (nz:∀U,R.eval U≠0) (live:Integrable X (prior G n)) (people:Occupancy o M)
    (width:∀i,0<w i) (tariff:2≤R.p.supportExponent) (hard:0≤t) (pos:0<η) (small:η≤1)
    (gas:((R.p.B+R.p.B+1:ℕ):ℝ)^4*(t+M*siteFactor R.p.B*η)≤1/2)
    (fees:((R.p.B+R.p.B+1:ℕ):ℝ)^4*Ribbons.Salt.scent R.p.B M (R.p.supportExponent+1/2) 1 η 1 t≤1/2 ∧
      Real.exp (Ribbons.Salt.scent R.p.B M (R.p.supportExponent+1/2) 1 η 1 t)-1≤1) :
    MenuBoard R P X o (fun i=>η*w i/Real.exp (R.p.supportExponent+1/2)) (R.p.supportExponent-2) 1:=by
  let policy:Pantry.Policy (L) (J) (J):=fun _=>Finset.mem_powerset.mpr (Finset.subset_univ _)
  have same (i:I):(L).Solo i:=fun _ h=>h.symm
  have cap' : Alcove R P X o w t η 1:=by
    obtain ⟨E,K,ψ,c,he,hk,hb,hf,hg,hc,hq,hs,ident⟩:=cap.chamber
    exact ⟨cap.clef,cap.value,cap.tally,cap.price,E,K,ψ,c,he,hk,hb,hf,hg,fun i=>(hc i).trans (by norm_num),hq,hs,ident⟩
  have close (i:Unit×I):coverNumber R.p.B ({(o ∘ (T).twig) ((T).bunch i),o i}:Support n)≤1:=by
    change coverNumber R.p.B ({o i,o i}:Support n)≤1
    simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using alone R.p.B (o i)
  have count (i:Unit×I):((T).contents i).card≤1:=by rw [content,Finset.card_singleton]
  obtain ⟨P',post,kept⟩:=Pantry.breakfast (o:=o) (L) policy (by decide:0<(1:ℕ)) count cap' valid stock tariff
    (S:=Finset.univ) (fun i _=>same i) width hard pos small people people close gas fees.1 fees.2 nz live
  have sections:P'=P:=funext (fun i=>(kept i).1 (Finset.mem_univ _))
  have surface (U): Pantry.pilot (L) policy (X U) = X U:=by
    ext s
    change (X U).part ⟨((T).plena _).val,_⟩=(X U).part s
    congr 1; apply Subtype.ext; ext i; rw [Fibers.reaped]; rfl
  have prices (i:Unit×I): (∏ j∈(T).contents i,Fibers.Salt.tow w (R.p.supportExponent+1/2) (η/1) 1 j) =
      η*w i/Real.exp (R.p.supportExponent+1/2):=by
    rw [content,Finset.prod_singleton]
    simp [Fibers.Salt.tow]
  have homes:o ∘ (T).twig=o:=by funext i; cases i; rfl
  simpa only [sections,surface,homes,Nat.cast_one,prices] using post

end YM.Integration.WilsonThermometerUnchangedGrouping
end
