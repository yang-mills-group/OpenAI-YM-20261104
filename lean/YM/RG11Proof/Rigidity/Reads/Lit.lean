import YM.RG11Proof.Rigidity.Reads.Listing

/-!
# Meet the crews with fixed local B fields at clocks
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Reads
open Maxwell Maxwell.Free Wick Crowd Prism Function Tensor
open scoped BigOperators ContDiff Classical
variable {G:Gauge}{I:Type}

def bloc (G : Gauge) (p : Panel) : Cast G := (Finset.univ:Finset G.ColorIndex).toList.map
    (fun i:G.ColorIndex=> (1,[⟨0,i,cell p.1.1.1 p.1.1.2⟩,⟨0,i,cell p.2.1.1 p.2.1.2⟩]))
lemma bloc_team (p : Panel) : canon (bloc G p) = team G (cell p.1.1.1 p.1.1.2) (cell p.2.1.1 p.2.1.2) := by
  rw [canon,bloc,List.map_map, Finset.sum_map_toList]; unfold team
  apply Finset.sum_congr rfl; intro i _; simp [emits,Dart.write,Dart.flip,Free.letter,bit]

lemma bloc_times (p : Panel)(h : p.1.2=p.2.2)(W : Crowd G)(m : Word G→ℝ):
    (W.panel p).asks m=(times (ticket p.1.2 (bloc G p)) W).asks m := by
  rw [panelRead,times_read,ticket_read,issue,bloc,List.map_map,Finset.sum_map_toList]
  apply Finset.sum_congr rfl; intro i _
  simp only [Function.comp_apply,one_mul,travel,List.map_cons,List.map_nil,painting,toss,← h]

def withB (p : Panel) : E4×(Sum Panel I):= (p.1.2,Sum.inl p)
def without (p : E4 × I) : E4×(Sum Panel I):=(p.1,Sum.inr p.2)
def mixture (p : List Panel)(l : Board I): Board (Sum Panel I):= p.reverse.map withB ++ l.map without

lemma societies (A : Performer G I) (l : Board I) (p : List Panel)(hp:∀ i∈p,i.1.2=i.2.2) (m : Word G→ℝ):
    (run p (A.society l)).asks m= (carol (scoreAt (Sum.elim (bloc G) A.slate) (mixture p l))).asks m:= by
  induction p using List.reverseRecOn generalizing l m with
  | nil=>
    change (A.society l).asks _=_
    congr 1; unfold mixture scoreAt; simp only [List.reverse_nil,List.map_nil,List.nil_append,List.map_map]; clear hp
    induction l with
    | nil=>rfl
    | cons a l h=>rw [Performer.society,List.map_cons,carol]; exact congrArg (times _) h
  | append_singleton p w ih =>
    have hm : w.1.2=w.2.2:= hp w (by simp)
    have hh (i) (h:i∈p): i.1.2=i.2.2:=hp i (by simp [h])
    rw [run_append,run,run,bloc_times w hm]
    rw [show mixture (p++[w]) l=withB w::mixture p l from by simp [mixture],scoreAt,List.map_cons,carol]
    rw [times_read,times_read]; dsimp only [withB,Sum.elim_inl]
    congr 1; funext i
    exact ih _ hh _ -- m was fixed in ih, need generalize

lemma lights_match {S : Finset E4}{L:List Panel} (h:Lamps S L):∀ p∈L,p.1.2=p.2.2:=by
  induction L generalizing S with | nil=>simp| cons a L ih=> intro v hv; rcases List.mem_cons.mp hv with rfl|he; exact h.1; exact ih h.2.2 v he
lemma lights_stay {S : Finset E4}{L:List Panel} (h:Lamps S L) : (L.map (fun p=>p.1.2)).Nodup ∧ ∀ p∈L,p.1.2∉S:=by
  induction L generalizing S with
  | nil=>simp
  | cons a L ih=>
    obtain ⟨hL,hV⟩:=ih h.2.2
    refine ⟨List.nodup_cons.mpr ⟨?_,hL⟩,fun p hp=>?_⟩
    · rintro hh; obtain ⟨p,hp,he⟩:=List.mem_map.mp hh; exact hV p hp (by rw [he]; simp)
    rcases List.mem_cons.mp hp with rfl|hi; exact h.2.1; exact fun hi' => hV p hi (by simp [hi'])

lemma curtains_with {l : Board I} (h : Curtained l){p : List Panel}(hp : Lamps (borders l) p) : Curtained (mixture p l):=by
  unfold Curtained mixture; rw [List.map_append,List.map_map,List.map_map]
  change ((p.reverse.map fun i=>i.1.2)++l.map Prod.fst).Nodup
  rw [ List.map_reverse]
  obtain ⟨he,hs⟩:= lights_stay hp
  refine List.nodup_append.mpr ⟨(List.reverse_perm _).nodup_iff.mpr he,h,?_⟩
  intro a h₁ b hb heq
  obtain ⟨t,ht,hta⟩:= List.mem_map.mp (List.mem_reverse.mp h₁)
  exact hs t ht (List.mem_toFinset.mpr (by rw [hta]; exact (heq : a=b).symm ▸ hb))

/-- The input is still honest simultaneous correlations (with free Bs), not
individual response of each operator versus fixed testers. -/
lemma freezeDesert {A B:Performer G I}(h:A.deadline=B.deadline)
    (hP : ∀ (n : ℕ)(x: Points n),x∈conf n→ ∀ f : Fin n→Panel ⊕ I,
      moment G x (fun i=> canon (Sum.elim (bloc G) A.slate (f i)))=moment G x (fun i=> canon (Sum.elim (bloc G) B.slate (f i)))) : Desert A B:= by
  refine ⟨h,fun l hl p hp=> ?_⟩
  rw [societies A l p (lights_match hp),societies B l p (lights_match hp)]; apply Complex.ofReal_injective
  rw [← page (curtains_with hl hp),← page (curtains_with hl hp)]; exact hP _ _ (curtains (curtains_with hl hp)) _

end YM.RG11.Rigidity.Reads
