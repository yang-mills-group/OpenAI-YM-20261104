import YM.RG11Proof.Rigidity.Reads.Ink

/-!
# Free Wick test represented by crews of word labels
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Reads
open Maxwell Maxwell.Free Wick Crowd Prism Function Tensor
open scoped BigOperators ContDiff Classical

variable {G : Gauge} {n : ℕ}
abbrev Crew (G : Gauge) (n : ℕ) := List (Fin n × Cast G)
abbrev Score (G : Gauge):= List (E4 × Cast G)

def carol : Score G→ Crowd G
  | []=> [(1,[])]
  | a::l=> times (ticket a.1 a.2) (carol l)
def singing (l : Crew G n) (j:Fin n) := (l.map (fun a=>if j=a.1 then canon a.2 else 1)).prod

def heard (x : Points n) (M : List (Fin n× Dart G)) : Word G:= M.map (fun a=> Pig.mk (x a.1) a.2)

abbrev planted (M : List (Fin n× Dart G)) (j : Fin n) : WickPol G:= bag Prod.fst (fun a=>a.2.flip) M j

def lines (x : Points n) (l : Crew G n) := l.map fun a=> (x a.1,a.2)

def scoreAt {ι : Type}(f : ι →Cast G) (L : Board ι) : Score G:= L.map fun a=> (a.1,f a.2)

private lemma planted_up (i : Fin n) (a : Article G) (M : List (Fin n× Dart G)) :
    let u:= planted (M++List.map (fun q=> (i,q)) a)
    u = planted M * fun j=> if j=i then emits a else 1 := by
  intro u; ext1 j; unfold u planted; rw [bag_merge]; congr 1
  unfold bag emits; by_cases H:j=i <;> simp [H,List.map_map,Function.comp_def]; rfl

-- scalar one-site assembly helper before recursing on remaining sites
private lemma solo (x : Points n)(u t : Fin n→WickPol G)(a: Fin n)(C : Cast G) :
    let m (Q : WickPol G) := fun i=>u i*(if i=a then Q * t i else t i)
    moment G x (m (canon C)) = (C.map (fun i=> (i.1:ℂ)* moment G x (m (emits i.2)))).sum := by
  intro m
  let f := (moment G x).toLinearMap (u*t) a
  have he (Q : WickPol G) : moment G x (m Q)=f (u a*t a*Q):=by
    rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; unfold m
    by_cases h:i=a <;> simp [h,mul_assoc,mul_comm (t a)]
  simp_rw [he]
  induction C with
  | nil=> simp [canon]
  | cons i l ih=>
    change f (_*(_ + canon l))=_ + _
    rw [mul_add,map_add,ih,mul_smul_comm,map_smul]; rfl

set_option maxHeartbeats 160000 in
lemma script (x : Points n) (hx : x∈conf n) (l : Crew G n) (M : List (Fin n× Dart G)) :
    moment G x (planted M * singing l)= ((carol (lines x l)).asks (fun q=> meter (heard x M++q)):ℂ) := by
  induction l generalizing M with
  | nil=>
    simp only [lines,List.map_nil,carol,asks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,one_mul, List.append_nil]
    rw [show planted M*singing [] = planted M from mul_one _,meter_full,bag_rec Prod.fst (fun a : Fin n × Dart G=>a.2.flip) M hx]
    simp [heard,List.map_map,Function.comp_def,Pig.full]
  | cons i L ih=>
    obtain ⟨i,C⟩:=i
    have hs (j : Fin n): singing ((i,C)::L) j=if j=i then canon C*singing L j else singing L j:=by simp [singing,ite_mul]
    simp only [Pi.mul_def, List.map_cons,lines, carol]
    simp_rw [hs]
    rw [show moment G x (fun j=> planted M j*(if j=i then canon C*singing L j else singing L j)) =_ from solo x (planted M) (singing L) i C]
    rw [times_read,ticket_read]
    have hp (u : Article G) :
        moment G x (fun j=> planted M j*(if j=i then emits u * singing L j else singing L j)) =
          ((carol (lines x L)).asks (fun q=>meter (heard x M++(travel (x i) u ++ q))):ℂ) := by
      let Y := List.map (fun a:Dart G=>(i,a)) u
      rw [show (fun j=> planted M j*(if j=i then emits u * singing L j else singing L j))= planted (M++Y)*singing L from ?_,ih (M++Y)]
      · simp [Y,heard,List.map_map,Function.comp_def,travel,List.append_assoc]
      rw [planted_up i u]; ext1 j; by_cases h : j=i <;> simp [h,mul_assoc]
    unfold issue; rw [show ∀ p : List ℝ,(↑p.sum:ℂ)=(p.map (↑)).sum from fun _=> map_list_sum Complex.ofRealHom _,List.map_map]; congr 1; apply List.map_inj_left.mpr; intro q _
    dsimp only [Function.comp_apply]; rw [hp q.2,Complex.ofReal_mul]; rfl

end YM.RG11.Rigidity.Reads
