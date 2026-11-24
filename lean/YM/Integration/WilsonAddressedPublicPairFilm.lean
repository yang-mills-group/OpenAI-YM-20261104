import YM.Integration.WilsonAddressedPublicOpticalPair
import YM.Integration.WilsonOriginalBlissMixedGram

/-! The actual reflected two-field moment on the original finite Wilson film. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonAddressedPublicPairFilm
open Function Filter Finset Lattice RG Wilson Source Labels Cells OPE Extraction Spec
open Table PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee width)
open WilsonAddressedPublicOpticalPair (length)
open Push.RelayDifference (oriented)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)
local notation "C" => R.family

theorem reflected {d N p:ℕ}(live:(C).ref d ≤ N)(x:(C).label d)(a:Axis)
    (o:Site ((C).side N p))(U:Config G ((C).side N p)):
    oriented ((C).O N p x 0) true (Signed.mirror a) o U=(C).O N p ((C).book.adj d a x) o U:=by
  change star ((C).O N p x 0 (pull (Signed.mirror a) o U))=_
  rw [←(C).reality R.makes live x 0 (pull (Signed.mirror a) o U)]
  change _=(C).O N p (((C).labels.level d).act (Signed.mirror a).ortho (star x)) o U
  simpa [affine] using
    ((C).rotated R.makes live (star x) (Signed.mirror a) 0 o U).symm

theorem direct {d N p:ℕ}(live:(C).ref d ≤ N)(x:(C).label d)
    (o:Site ((C).side N p))(U:Config G ((C).side N p)):
    oriented ((C).O N p x 0) false 1 o U=(C).O N p x o U:=by
  change (C).O N p x 0 (pull 1 o U)=_
  have turn:=((C).rotated R.makes live x 1 0 o U).symm
  rw [show affine (1:Signed) o 0=o by simp [affine]] at turn
  change _=(C).O N p ((C).book.mirrorGroup d 1 x) o U at turn
  rw [(C).book.mirror_one] at turn
  exact turn

variable {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{r:Fin 2→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin 2→Fin (D+1))(v:∀i,S.Field (d i).val)(b:Fin 2→Bool)
local notation "A" => R.family.path.levels
local notation "fees" => (fun i=>fee F (B i) (d i) (v i) (b i))
local notation "widths" => (fun i=>width F (B i) (d i) (v i) (b i))

def reading (a:Axis)(N p:ℕ)(o:Fin 2→Site ((C).side N p)):ℂ:=
  (C).ensemble (grades (d 0).val (d 1).val) o
    (columns R a (d 0).val (d 1).val ((((B 0).rows (d 0)).arm (b 0) (v 0)).source (N,p))
      ((((B 1).rows (d 1)).arm (b 1) (v 1)).source (N,p)))

theorem original (cash:Trace.Terrace.PostT (A))(simple:G.Simple)(house:∀i,Housed F (B i)):
    ∃first:ℕ,∀k:ℕ,first ≤ k → (∀i,widths i ≤ k) →
    let m:=min (widths 0) (widths 1)
    let wall:=max (length F (B 0) (b 0)) (length F (B 1) (b 1))
    0 < m → ∀ᶠ w:ℕ×ℕ in f.fuse,∀a:Axis,∀(L:Type)[Fintype L]
      (u:L→Fin 2→Site ((C).side w.1 w.2))(μ:L→ℂ),
    (∀i i' t,i≠i' → (A).clock.monitor k*wall < (C).S.a w.1*(separation (u t i) (u t i'):ℝ)) →
    ‖∑t,μ t*reading R F B d v b a w.1 w.2 (u t)‖ ≤ (∑t,‖μ t‖)*∏i,fees i:=by
  classical
  obtain ⟨J,receipt⟩:=WilsonAddressedPublicOpticalPair.original F B d v b cash simple house
  refine ⟨J,?_⟩
  intro k late bound m wall pos
  have live:∀ᶠ w:ℕ×ℕ in f.fuse,∀i:Fin 2,(C).ref (d i).val ≤ w.1:=by
    apply eventually_all.mpr
    intro i
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop _
  filter_upwards [receipt k late bound pos,live] with w paid truthful
  intro a L _ u μ apart
  let hand:Fin 2→Bool:=Fin.cons true (fun _=>false)
  let axes:Fin 2→Signed:=Fin.cons (Signed.mirror a) (fun _=>1)
  have actual:=paid L u μ (fun _=>hand) (fun _=>axes)
    (fun _ i=>by fin_cases i <;> rfl) (fun t i i' h=>apart i i' t h)
  convert actual using 2
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  change (C).omega w.1 w.2 _ = _
  apply congrArg (moment ((C).beta w.1 w.2))
  funext U
  rw [Fin.prod_univ_two,Fin.prod_univ_two]
  change _*_=oriented _ true (Signed.mirror a) _ U * oriented _ false 1 _ U
  exact congrArg₂ (·*·)
    (reflected R (p:=w.2) (truthful 0) ((((B 0).rows (d 0)).arm (b 0) (v 0)).source w) a (u t 0) U).symm
    (direct R (p:=w.2) (truthful 1) ((((B 1).rows (d 1)).arm (b 1) (v 1)).source w) (u t 1) U).symm

end YM.Integration.WilsonAddressedPublicPairFilm
end
