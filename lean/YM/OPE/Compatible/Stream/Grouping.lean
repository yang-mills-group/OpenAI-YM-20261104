import YM.OPE.Compatible.Stream.Settle
/-!
# Meeting charge in curvature norm

`Radius` here is exponential cover width, retained. Difference estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Frequency
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
variable {α β γ:Type*}[Fintype α][Fintype β] {ι:Type*}[Fintype ι]
-- sum
omit [Fintype α] [Fintype β]
lemma row_strips {A:ι→Row α β} {η x:ℝ}(h:∀ i,(A i).strip η x) : (∑ i:ι, A i).strip η ((Fintype.card ι:ℝ)*x) := by
    intro a b; rw [show (∑ i:ι,A i) a b=(fun x=> ∑ i,A i a b x) by ext x; simp]; exact width_sum_finite (fun i=> h i a b)
lemma whole_plus {A B:Row α β}(a:Whole A)(b:Whole B):Whole (A+B):=by
    have h:A+B= plusRows A B:=by funext i j p; simp [plusRows, minusRows,scaleRows]
    rw [h]; exact a.plus b
lemma whole_region {A:ι→Row α β}(h:∀ i, Whole (A i))(p:Momentum)(hp:physical p): (∑ i:ι,A i).read p=∑ i, (A i).read p:=by
    suffices h:∀ s:Finset ι, Whole (∑ i∈s,A i) ∧ (∑ i∈s,A i).read p=∑ i∈s,(A i).read p from (h _).2
    classical
    intro s; induction s using Finset.induction_on with
    | empty=>simp [barren_whole]
    | insert i s hi ih=>
       rw [Finset.sum_insert hi,Finset.sum_insert hi]; refine ⟨whole_plus (h i) ih.1,?_⟩
       rw [← ih.2, show A i + _= plusRows (A i) (∑ i∈s,A i) from ?_]; exact (h i).read_plus ih.1 hp
       funext k j p; simp [plusRows,minusRows,scaleRows]
lemma acts_region {A:ι→Row α β}(h:∀ i, Whole (A i))(c:Side): (∑ i:ι,A i).acts c=∑ i, (A i).acts c:=by
    suffices h:∀ s:Finset ι, Whole (∑ i∈s,A i) ∧ (∑ i∈s,A i).acts c=∑ i∈s,(A i).acts c from (h _).2
    classical
    intro s; induction s using Finset.induction_on with
    | empty=>simp [barren_whole]
    | insert i s hi ih=>
       rw [Finset.sum_insert hi,Finset.sum_insert hi]; refine ⟨whole_plus (h i) ih.1,?_⟩
       rw [← ih.2, show A i + _= plusRows (A i) (∑ i∈s,A i) from ?_]; exact (h i).acts_plus ih.1 c
       funext k j p; simp [plusRows,minusRows,scaleRows]
open Flight
variable {η U a B:ℝ} {L:Side}{A: Cross L (TypeFace 2) (TypeFace 2)} {Q:Row (TypeFace 2) (TypeFace 2)}
lemma cashCarry {l:List Axis} {X : Cross L (TypeFace 2) (TypeFace 2)} (hη:0 ≤ η)(H:A.strip η (U/L.val^2)) (g: Q.strip η a)(hL:X.strip η (U/L.val^3)) (hx:(pathJet (TypeFace 2) l).strip η B) :
   let m:=(Fintype.card (TypeFace 2):ℝ)
   (composeRows (net A (fineCompose Q X)) (pathJet (TypeFace 2) l)).strip η (m^3*a*B*U^2/L.val):=by
    intro m; apply strip_mono (strip_compose hη (strip_compose (P:=transRows A) hη (strip_trans H) (strip_fine hη g hL)) hx) le_rfl
    apply le_of_eq; unfold Co; rw [Fintype.card_prod,site_card]; dsimp only [m];push_cast; field_simp
lemma whole_cull_zero {m:Type} [Fintype m][DecidableEq m] {x:Row m (TypeFace 2)}(h:Whole x)(i:Axis): (composeRows x (pathJet (TypeFace 2) [i])).read 0=0:=by
    have he: physical (0:Momentum):= by unfold physical;simp
    rw [h.read (jet_whole _ _) he,jet_read _ _ he]; simp [listChip]
end YM.Next.Free.Frequency
