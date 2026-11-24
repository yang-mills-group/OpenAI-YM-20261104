import YM.RG11Proof.Fields.Diagnostic
import YM.Extra.WEAK_SCALING_ACTLAW.Four
/-! Ordinary-vs-connected issue for the diagnostic. Work POINTWISE on
separated coefficients before smearing with its *joint* profile. Thus no
factorization of tests or tacit vanishing of vacuum pieces. Connected equation
here is only for three labels in this geometry; using eq-of-unit/null in any
contact *not* justified. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries Function Set Labels Maxwell Pert.Position Extra.FD Pert.Triangle Pert.RawLabels Filter
open scoped Classical BigOperators
variable {G:Gauge} {F:Frames G}(hg:G.Simple) {d:ℕ} (h:6 ≤ d)
private abbrev Slot3 := Fin 3

-- Unit insertion at one of the three points. Ordering inferred at deletion.
def dropX (x:Points 3)(k:Fin 3):Points 2 := Points.tail (Points.rearrange (Equiv.swap 0 k) x)
def dropLabels {α:Type*}(s : Fin 3→α)(k:Fin 3):Fin 2→α:=Fin.tail (s ∘ Equiv.swap 0 k)

theorem pair_drop (T:(freeTable F).Basic) {x:Points 3} (hx:x∈conf 3)(p : Fin 3→ E F d)(k:Fin 3):
   visible F d (dropX x k) (dropLabels p k)=visible F d x (update p k ((freeTable F).unit d)):= by
  let Z:=freeTable F
  let w:Fin 3→Z.Tag:= fun i=>Sigma.mk d (update p k (Z.unit d) i)
  let q:=Equiv.swap (0:Fin 3) k
  change Z.useAt Z (dropX x k) (fun i=>Sigma.mk d (dropLabels p k i))= Z.useAt Z x w
  rw [← Z.class_perm Z T.toSymmetric q hx]
  have he : w ∘ q = Fin.cons (α:=fun _=>Z.Tag) ⟨d,Z.unit d⟩ (fun i=>Sigma.mk d (dropLabels p k i)):= funext fun i=> by
    refine Fin.cases ?_ (fun i=>?_) i
    · simp [w,q]
    have hk:q i.succ ≠ k:=by rw [← show q 0=k from Equiv.swap_apply_left ..]; exact q.injective.ne i.succ_ne_zero
    simp only [w,dropLabels,Fin.cons_succ,comp_apply,update_of_ne hk, Fin.tail]
    rfl
  rw [he,Z.at_unit T (Points.rearrange_in q hx)]; rfl

private lemma unit_lower : (freeTable F).unit 6 ∈ lower F 4 6 := by
   rw [← staircase F (show 4≤6 by decide)]
   refine ⟨(freeTable F).unit 4, ?_⟩
   apply writes_inj F 6; rw [up_write,writes_unit,writes_unit]

include hg

theorem pair_null (T:(freeTable F).Basic){x:Points 3}(hx:x∈conf 3)(k:Fin 3):
    visible F d (dropX x k) (dropLabels (Fields.triple h F) k)=0:= by -- arguments fix
   rw [pair_drop T hx]
   -- move **back** to six to use free_point_stability with the constant function
   have hu : update (Fields.triple h F) k ((freeTable F).unit d) = up F h ∘ update (basic F) k ((freeTable F).unit 6):= funext fun i=>by
     by_cases he:i=k
     · subst i
       simp only [comp_apply,update_self]; symm; apply writes_inj F d; rw [up_write,writes_unit,writes_unit]
     rw [update_of_ne he,comp_apply,update_of_ne he]; rfl
   rw [hu,up_moment]
   exact free_point_stability hg F hx (fun _=> (freeTable F).unit 6) (fun _ _=> unit_lower) k

omit hg in
theorem mean_null (x:Points 1) (i:Fin 3):
    visible F d x (fun _=>Fields.triple h F i)=0:=by
  rw [writes_pair,Extra.WeakScaling.Color.one_wick]
  change Maxwell.probe 0 (writes F d (up F h (basic F i)))=_
  rw [up_write]
  by_cases hi:i=0
  · subst i
    let b:=writes F 6 (basic F 0)
    have hv:=reverse_read (0:TaylorTower G) b
    rw [neg_zero,(show reversePol G b=-b from odd_reversed F),_root_.map_neg] at hv
    exact neg_eq_self.mp hv -- lemma?
  rw [write_minus F i hi, jet_value,read_u]
  simp

private abbrev PS := PowerSeries ℂ

def conn (large : Points 3→PS) (small : Points 3→Fin 3→PS) (solo : Points 3→Fin 3→PS) (x : Points 3) :=
   large x - ∑ i,small x i * solo x i + PowerSeries.C (2:ℂ) * ∏ i, solo x i

-- Caller uses actual one-point positions with the common centering geometry
-- (pass `vacuole` e.g. Fin.cons single x k). No assumption that positive-order
-- means vanish; at next orders they can and do matter.
theorem agree (T:(freeTable F).Basic)
    (large : Points 3 → PS) (small solo : Points 3→Fin 3→PS)
    (vacuole : Points 3→Fin 3→Points 1)
    (hv : ∀ x∈conf 3,∀ i,constantCoeff (solo x i)=visible F d (vacuole x i) (fun _=>Fields.triple h F i))
    (hp : ∀ x∈conf 3,∀ i,constantCoeff (small x i)=visible F d (dropX x i) (dropLabels (Fields.triple h F) i)) :
    EqOn (fun x=> coeff 1 (conn large small solo x)) (fun x=> coeff 1 (large x)) (conf 3):=by
  intro x hx
  have hs(i):constantCoeff (solo x i)=0:= (hv x hx i).trans (mean_null ..)
  have he(i):constantCoeff (small x i)=0:= (hp x hx i).trans (pair_null hg h T hx i)
  unfold conn
  simp [map_sub,map_add,map_sum, coeff_one_mul,hs,he,Fin.prod_univ_three]
end YM.RG11.Fields
