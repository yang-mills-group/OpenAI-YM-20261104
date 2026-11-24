import YM.MergeProof.Hens
/-!
 # Exact coefficient difference with all lower terms already aligned.
 Covers rank>2 cases when differences start at that high joint weight, or rank-two
 in Names by restoring paired singletons & vacuum. Tracking output as a single
 virtual singleton throughout avoids treating ratios of reps or dividing by a partition.
 -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.RG05.Strand
open Finset MeasureTheory Lattice Wilson RG Push Marker Extra.Histories MergeProof MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type*}[DecidableEq V] {B:Census V} (a: B.Mode)(v:V)
local notation "P"=> Poly B
abbrev Trim (a:B.Mode)(p:Poly B): Prop:=∀ i:B.Mode, i.val.card < a.val.card→ p.part i=0
private lemma payload (p p':Poly B)(a:B.Mode):(p-p').part a=p.part a-p'.part a:=rfl
namespace Trim
variable {x y z:Poly B}(h:Trim a x)
include h
lemma mul_lower (y:Poly B): Trim a (x*y):=by
    intro i hi; rw [Poly.part_mul]; refine sum_eq_zero fun b _=> sum_eq_zero fun c _=>?_ ; split; next hz=> rw [h b ((card_le_card (show b.val⊆i.val from hz.2 ▸ subset_union_left)).trans_lt hi),zero_mul]
    rfl
lemma mul_top (y : Poly B): (x*y).part a=x.part a*y.part B.quiet:=by
    rw [Poly.part_mul, Finset.sum_eq_single a]; rw [Finset.sum_eq_single B.quiet]; rw [if_pos ?_]; rw [Poly.wind]; exact (Poly.vacuum ..).2 rfl
    · intro b _ hb; split; next h=>
          have he : a.val.card = a.val.card+b.val.card:=by nth_rw 1 [←h.2]; rw [card_union_of_disjoint h.1]
          exact False.elim (hb (Subtype.ext (card_eq_zero.mp (by omega))))
      rfl
    · simp
    · intro i _ he; apply sum_eq_zero; intro j _; split; next hz=>
          have hj : a.val.card=i.val.card+j.val.card:=by rw [← hz.2,card_union_of_disjoint hz.1]
          rw [h _ _,zero_mul]; apply (card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h=> he (Subtype.ext h) ⟩)); exact hz.2 ▸ subset_union_left
      rfl
    simp
end Trim
structure Graded (a:B.Mode) (v:V) (x y z:Poly B) : Prop where
    same : Trim a (x-y)
    quiet : y.part B.quiet=z.part B.quiet
    cost : (x-y).part a=z.part (B.fire v)
namespace Graded
variable {x y z x' y' z':Poly B} (h:Graded a v x y z) (hq:Graded a v x' y' z')
include h
include hq in
lemma joint : Graded a v (x+x') (y+y') (z+z'):=by
    have hr : x+x'-(y+y')= x-y+(x'-y'):=by abel
    refine ⟨hr.symm ▸ ?_,?_,?_⟩
    · intro i hi; rw [Poly.part_plus,h.same i hi,hq.same i hi,zero_add]
    · rw [Poly.part_plus, h.quiet,hq.quiet,Poly.part_plus];
    rw [hr,Poly.part_plus,h.cost,hq.cost, Poly.part_plus]
lemma scale (s:ℂ): Graded a v (s • x) (s • y) (s • z):=by
    refine ⟨?_,?_,?_⟩
    · intro i hi; rw [← smul_sub,Poly.part_smul,h.same _ hi,mul_zero]
    · rw [Poly.part_smul,h.quiet,Poly.part_smul]
    rw [← smul_sub,Poly.part_smul,h.cost,Poly.part_smul]
include hq in
lemma shock (hv:a ≠ B.quiet) : Graded a v (x*x') (y*y') (z*z'):=by
    have he:x*x'-y*y'=(x-y)*x'+(x'-y')*y:=by ring
    refine ⟨he.symm ▸ (fun i hi=> by rw [Poly.part_plus,h.same.mul_lower a x' i hi,hq.same.mul_lower a y i hi,zero_add]),?_,?_⟩
    · rw [Poly.quiet_mul ,h.quiet,hq.quiet,Poly.quiet_mul]
    rw [he,Poly.part_plus, h.same.mul_top, hq.same.mul_top,h.cost,hq.cost, MergeProof.Accent.shock, h.quiet];
    have hu:0<a.val.card:= card_pos.mpr (nonempty_iff_ne_empty.mpr fun z=> hv (Subtype.ext z))
    have h0':= hq.same B.quiet (by simp [Census.quiet]; exact card_pos.mp hu); rw [payload, sub_eq_zero,hq.quiet] at h0'; rw [h0']; ring
omit h
lemma nil : Graded a v 0 0 0:=by refine ⟨fun x _=> ?_,rfl,?_⟩ <;> rw [sub_self] <;> rfl
lemma empty : Graded a v 1 1 1:= by refine ⟨(fun x _=>by rw[sub_self];rfl),rfl,?_⟩; rw [sub_self,Poly.one_part,if_neg (B.fire_hot _)];rfl
include h
lemma power (k:ℕ)(hv:a ≠ B.quiet): Graded a v (x^k) (y^k) (z^k):=by induction k with | zero=> simp only [pow_zero]; exact empty a v| succ k IH=> simpa only [pow_succ] using IH.shock a v h hv
omit h
variable {I:Type*} (A:Finset I)(F X Y:I→ Poly B) (hx:∀ i∈A, Graded a v (F i) (X i) (Y i))
include hx
lemma fin_degree : Graded a v (∑ i∈A,F i) (∑ i∈A,X i) (∑ i∈A,Y i):= by
    induction A using Finset.induction_on with
    | empty => simpa only [sum_empty] using Graded.nil a v
    | insert i A hi ih=> rw [sum_insert hi, sum_insert hi,sum_insert hi]; exact (hx i (mem_insert_self ..)).joint a v (ih (fun i hi=>hx i (mem_insert_of_mem hi)))
lemma fin_degree_prod (ha:a ≠ B.quiet): Graded a v (∏ i∈A,F i) (∏ i∈A,X i) (∏ i∈A,Y i):= by
    induction A using Finset.induction_on with
    | empty => simpa only [prod_empty] using Graded.empty a v
    | insert i A hi ih=> rw [prod_insert hi, prod_insert hi,prod_insert hi]; exact (hx i (mem_insert_self ..)).shock a v (ih (fun i hi=>hx i (mem_insert_of_mem hi))) ha
omit hx
open Accent
variable {n:Side} {u:Support n}{α β δ:Box n→Poly B}
lemma field (h:a ≠ B.quiet)(hp:∀ i,Graded a v (α i) (β i) (δ i)) : Graded a v (Accent.field α u) (Accent.field β u) (Accent.field δ u):= by
    apply Graded.fin_degree; intro i _; unfold grid; split_ifs; exact Graded.fin_degree_prod a v i α β δ (fun i _=>hp i) h; exact nil a v
variable [Fintype V]
include h
lemma pass (hv:a ≠ B.quiet) : Graded a v (Poly.pass x) (Poly.pass y) (Poly.pass z):= Graded.fin_degree a v _ _ _ _ (fun j _=> (h.power a v j hv).scale a v _)
end Graded
-- A leading-grade difference reduces exactly to an insertion; p itself need not be singleton.
open RG
variable [Fintype V] {G:Gauge} {n:Side}
    {F F':Config G n→ Poly B}{K K':Box n→Config G n→Poly B}{b: ℕ→Config G n→ℂ}{T:Rep G n}
    {f: Config G n→ℂ}{δ x:ℝ}
abbrev MarkDiff (a:B.Mode)(f:Config G n→ℂ)(F F':Config G n→ Poly B) := ∀ U, Trim a (F U-F' U)∧ (F U-F' U).part a=f U
include v
lemma plays (hp:T.activities.Valid T.p δ x)(hL: ∀ U,(F' U).part B.quiet=0)
      (hU:∀ i U,(K' i U).part B.quiet=profile T.activities (fun k=> Complex.ofReal ∘ T.activities.K k) i U) (he:MarkDiff a f F F') (hh:∀ i, MarkDiff a (profile T.activities b i) (K i) (K' i))
      (hz:a ≠ B.quiet) (hS:Dominated b) (U:Config G n)
      : (play T B K F U - play T B K' F' U).part a=coin T f b U:= by
    let g (U:Config G n):= Poly.send (B.fire v) (f U)
    let L (i:Box n) (U:Config G n):= Accent.bar T.activities B U i + Poly.send (B.fire v) (profile T.activities b i U)
    have hK : ∀ i, Graded a v (K i U) (K' i U) (L i U) :=by
         intro i; refine ⟨(hh i U).1,?_,?_⟩; rw [hU]; simp [L,Accent.bar,Poly.bead,(B.fire_hot v).symm]
         rw [(hh i U).2]; simp [L,Accent.bar,Poly.bead,B.fire_hot v]
    have hG: Graded a v (F U) (F' U) (g U):= ⟨(he U).1,hL U|>.trans (show _ = (g U).part B.quiet from by simp [g,(B.fire_hot v).symm]),by rw [(he U).2]; simp [g]⟩
    have hx: Graded a v (play T B K F U) (play T B K' F' U) (play T B L g U):= ((hG.pass a v hz).shock a v (Graded.field a v hz hK) hz).scale a v _
    rw [hx.cost]; have hp:(play T B L g U).part (B.fire v)=coin T (fun U=> (g U).part (B.fire v)) b U:= by
         apply beach T B L g U (fun _=> b) hp _ _ v (hS.summable U) _
         exact fun i=> (hK i).quiet.symm.trans (hU i U)
         simp [g,(B.fire_hot v).symm]
         exact fun i=> (hK i).cost.symm.trans (hh i U).2
    simpa [g] using hp
end YM.RG05.Strand
