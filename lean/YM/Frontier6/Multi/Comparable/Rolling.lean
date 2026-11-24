import YM.Frontier6.Multi.Comparable.Deacon
import YM.Frontier6.Multi.Tale.Product

/-! Aperture and averaging of compact-orbit detectors on *any* Permit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Spec Tale Fareway
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S:Table C.book}
variable (K:Final C H S){ξ:Ultrafilter (ℕ×ℕ)}{T:Fareway I}{j k:I→ℕ}{a b:ℝ}
namespace Fareway.Costs
lemma immured {Y:Type*}[SeminormedAddCommGroup Y]{X:Type*}[TopologicalSpace X][CompactSpace X](T:Fareway I)(p:X→Y)(hp:Continuous p)(q:I→X): T.Costs (p ∘ q) 0:=by
    obtain ⟨B,hB⟩:=(isCompact_univ.image (hp.norm)).bddAbove
    exact unlimited B (Eventually.of_forall fun i=> hB (mem_image_of_mem _ (Set.mem_univ (q i))))
end Fareway.Costs
variable {X:BasisRay S I}(h:Permit K T ξ j k X a)
set_option quotPrecheck false
lemma highlights {c:I→ E4} (p:Probe S) (g:I→Ortho) : Wide T (fun i (t:Option (Fin p.length))=>t.elim (c i) (fun x=>(p.roll K (g i)).exterior x+c i)) 0:=by
    obtain ⟨r,hr,h⟩:= gap_compact (isCompact_singleton (x:=Points.cons 0 p.exterior)) (singleton_subset_iff.mpr p.clear)
    apply Wide.uniform r hr; apply Eventually.of_forall; intro i u v hU; have hf:=roll_safe K p (h (Points.cons 0 p.exterior) (mem_singleton _)) (g i); cases u with
    | none=> cases v
             · exact False.elim (hU rfl)
             next v=> change r < ‖c i- ((p.roll K (g i)).exterior v+c i)‖; rw [norm_sub_rev]; simpa only [add_sub_cancel_right] using clear_exterior hf v
    | some u=> cases v
               · change r<‖(p.roll K (g i)).exterior u+c i-c i‖; rw [add_sub_cancel_right]; exact clear_exterior hf u
               next v=> change r < ‖(p.roll K (g i)).exterior u+c i-((p.roll K (g i)).exterior v+c i)‖; rw [add_sub_add_right_eq_sub]; exact clear_tail hf v u (fun e=>hU (congr_arg some e.symm))

variable (c:I→ E4)(d:ℕ)
local notation "V'"=>fun i=> written K (c i) (X i (c i))
include h
set_option maxHeartbeats 800000 in
lemma rolling_bill (hk:Bench C.S T k b)(hb:0<b)(hξ:ξ.toFilter≤H.fuse)(hW:Extraction.Wcmain C)(hG:Org.Grill C H) (p:Probe S)(g:I→Ortho) :
  T.Costs (fun i=> (p.roll K (g i)).tip K (written K (c i) (X i (c i)))) a:=by
    let d(i:Fin p.length):=(p.letter i).1; let v(i:Fin p.length) (z:I): S.Field (d i):= flying K p (g z) i
    let U(x:I)(i:Fin p.length):=(p.roll K (g x)).exterior i+c x
    have hp : ∀ j:Fin p.length,T.Costs (v j) 0:=fun j=> Fareway.Costs.immured T (fun g:Ortho=> flying K p g j) ((continuous_apply j).comp (fly_cont K p)) g
    have hz:= salary K h hk hb hξ hW hG c (fun j i=> U i j) d v (highlights K p g) hp (fun _=>none)
    let f : I→ℂ:= fun i=> poll S S (X i (c i)*∏ j:Fin p.length,letter S (U i j) ⟨d j,v j i⟩); apply Costs.cf (f:=f) hz; apply Eventually.of_forall; intro i
    rfl
lemma Permit.present : ∀ᶠ i in T.via, Visible K (c i) d (X i (c i)):=by
    obtain ⟨r,hr,hB⟩:= Frontier6.Safe.limits K d; obtain ⟨A,p,f,q,Z,L,hp,hq,hV⟩:=h.owns
    filter_upwards [eventually_all.mpr fun k:A=> eventually_all.mpr (fun b=> (hp k b).from_allowance (T.minted_c r hr) (by norm_num)), hV] with i hv h
    refine Visible.cf K ?_ (h.2.2.2 (c i)); unfold Plan.syntaxR; apply Visible.sum
    intro u _; apply Visible.scale; refine visibles K _ hB ?_ ?_ _
    · intro k b e; exact (h.1 _ timeAxis) (congr_arg (fun y:E4=> y timeAxis) (add_right_cancel e))
    intro j; simpa only [add_sub_cancel_right] using hv u j
omit h
lemma chamber_expense {X:I→Spelling S}(hv:∀ᶠ i in T.via,Visible K (c i) d (X i)) (hy:∀ (p:Probe S)(g:I→Ortho),T.Costs (fun i=> (p.roll K (g i)).tip K (written K (c i) (X i))) a): T.Costs (fun i=> album K (c i) d (X i)) a:=by
    intro b he
    let F (i):= album K (c i) d (X i); let t i:= Real.exp (T.scale i*b)
    let v (k:Fin (d+1))(p:(hand K k.val).list)(a:Bool)(i:I)(u:Ortho):= spotlight K (written K (c i) (X i)) a p.val u
    have h(k:Fin (d+1))(p:(hand K k.val).list)(a:Bool): ∀ᶠ i in T.via,∀ u, ‖v k p a i u‖ ≤ t i:= Fareway.Costs.uniform (fun g=> hy (p.val.flip K a) g) he
    filter_upwards [eventually_all.mpr fun k=> eventually_all.mpr fun p=>eventually_all.mpr (h k p),hv] with i hi hp
    let w:= t i; have hw:0 ≤ w:= (Real.exp_pos _).le
    refine (pi_norm_le_iff_of_nonneg hw).2 fun j=>(pi_norm_le_iff_of_nonneg hw).2 fun p=>(pi_norm_le_iff_of_nonneg hw).2 fun b=>(ContinuousMap.norm_le _ hw).2 fun g=>?_
    rw [album,(displayed K hp).seats]; exact hi j p b g
include h
lemma pricing (hk:Bench C.S T k b)(hb:0<b)(hξ:ξ.toFilter≤H.fuse)(hW:Extraction.Wcmain C)(hG:Org.Grill C H): T.Costs (fun i=> absorb K (c i) d (X i (c i))) a:= (chamber_expense K c d (h.present K c d) (rolling_bill K h c hk hb hξ hW hG)).mapped (detector K d)
end YM.Frontier6.Road
