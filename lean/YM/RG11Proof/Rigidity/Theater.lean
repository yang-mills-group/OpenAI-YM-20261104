import YM.RG11Proof.Rigidity.Hour
import YM.RG11Proof.Rigidity.Prism.Duel

/-!
# Associated-graded probe comparison on the physical word schedule
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free Crowd Prism Function
open scoped BigOperators Topology Classical

variable {I : Type} {G : Gauge}
structure Performer (G : Gauge) (N : Type) where
  deadline : N → ℕ
  slate : N → Cast G
  refund (i) : ∀ t ∈ slate i,ceilingG t.2≤ deadline i

abbrev Board (I : Type) := List (E4 × I)

def borders (L: Board I): Finset E4 := (L.map Prod.fst).toFinset
def Curtained (L: Board I) := (L.map Prod.fst).Nodup

namespace Performer
variable (A : Performer G I)
def society : Board I→ Crowd G
  | []=>[(1,[])]
  | i::L=> times (ticket i.1 (A.slate i.2)) (society L)

def goes (L : Board I) := (L.map (fun t=>A.deadline t.2)).sum

lemma society_live (L : Board I) : (A.society L).Live (borders L) := by
  induction L with
  | nil=>
    rintro w hw; obtain rfl:=List.mem_singleton.mp hw; simp
  | cons a l ih=>
    exact times_live (ticket_live (by simp [borders]) _) (ih.mono (by intro x hx; simp_all [borders]))

lemma society_limit (L : Board I) : ceilingC (A.society L) (A.goes L) := by
  induction L with
  | nil=> rintro w hw; obtain rfl:=List.mem_singleton.mp hw; rfl
  | cons a l h=>
    rw [goes,List.map_cons,List.sum_cons]
    unfold society; refine times_limit (fun t ht=> ?_) h
    rcases List.mem_map.mp ht with ⟨i,hi,rfl⟩
    exact (travels ..).symm ▸ A.refund a.2 i hi -- orientation?

def data (i : I×System (G:=G)) := topSample (A.slate i.1) (A.deadline i.1) i.2
lemma top_out (L : Board I) (Θ:G.ColorIndex→ Stream) (M:Mirror G) :
    (A.society L).asks (air M Θ (A.goes L)) =
    (List.map (fun i=> A.data (i.2,fun c=> Θ c i.1) M) L).prod := by
  induction L with
  | nil=> simp [society,air,asks,goes,airRaw,hue,cargo]
  | cons a l ih=>
    rw [List.map_cons,List.prod_cons]
    change (times (ticket a.1 (A.slate a.2)) (A.society l)).asks (air M Θ (A.deadline _ + A.goes _))=_
    rw [top_times _ (society_limit A l) Θ M, ih,top_tick]; rfl
    rintro t ht; rcases List.mem_map.mp ht with ⟨i,hi,rfl⟩; exact (travels ..).symm ▸ A.refund a.2 _ hi
end Performer

structure Desert (A B:Performer G I): Prop where
  matched : A.deadline=B.deadline
  lamps (L : Board I) : Curtained L → ∀ l : List Panel, Lamps (borders L) l →
    (run l (A.society L)).asks meter=(run l (B.society L)).asks meter

namespace Crowd
def wage (s:ℝ) (p:Crowd G) : Crowd G := p.map fun i=> (s*i.1,i.2)
def minus (W T:Crowd G): Crowd G:= W++wage (-1:ℝ) T
lemma minus_read (W T:Crowd G) (q:Word G→ℝ) : (minus W T).asks q=W.asks q-T.asks q:=by
  rw [minus,ask_append,sub_eq_add_neg]; congr 1
  unfold wage asks; induction T with | nil=>simp | cons a t ih=> simp only [List.map_cons,List.sum_cons,ih]; ring
lemma echoRead (W T:Crowd G) (q:Word G→ℝ) (p:List Panel) : (run p (minus W T)).asks q=(run p W).asks q-(run p T).asks q:=by
  simp_rw [palette.sums_read,minus_read]
  let l:=p.reverse.map (palette.showT G)
  simp_rw [show ∀ s t:ℝ,s-t=s+(-1)*t from fun _ _=> by ring,palette.add,palette.mul]

end Crowd

private lemma assignments (L : List (I×System (G:=G))) : ∃ l : Board I, Curtained l ∧
    ∃ Θ : G.ColorIndex→ Stream, List.map (fun i=> (i.2,fun c=> Θ c i.1)) l=L := by
  classical
  induction L with
  | nil=> exact ⟨[],List.nodup_nil,fun _ _ _=>0,rfl⟩
  | cons a L ih=>
    obtain ⟨l,hl,Θ,hT⟩:= ih
    haveI : Infinite E4:=inferInstance
    obtain ⟨z,hz⟩ := Infinite.exists_notMem_finset (borders l)
    refine ⟨(z,a.1)::l, List.nodup_cons.mpr ⟨fun h=>hz (List.mem_toFinset.mpr h),hl⟩,fun c x=> if x=z then a.2 c else Θ c x, ?_⟩
    rw [List.map_cons,← hT]; simp; intro i b hi
    have h : i≠z:= fun h=>hz (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(i,b),hi,h⟩)); simp [h]

theorem Desert.cast_shot {A B : Performer G I}(h : Desert A B)(c:G.ColorIndex) : Seen A.data B.data := by
  intro L
  obtain ⟨l,hl,Θ,hT⟩:= assignments L
  let W := A.society l; let T := B.society l
  let p := minus W T
  have he : Blind (borders l) p := ⟨?_,?_⟩
  rotate_right 2
  · rintro w hw i hi
    rcases List.mem_append.mp hw with hh|hh; exact A.society_live l _ hh _ hi
    obtain ⟨t,ht,rfl⟩:= List.mem_map.mp hh; exact B.society_live l t ht _ hi
  · intro l' hL'; exact (echoRead W T meter _).trans (sub_eq_zero.mpr (h.lamps l hl _ hL'))
  have hn : A.goes l=B.goes l:= by simp_rw [Performer.goes,h.matched]

  have hj (A : Performer G I) : Continuous (fun M=>chord A.data L M):= chord_cont _ (fun i=> samples_cont ..) _
  have hx := fatal c he (A.goes l) ?_ Θ
  · simp_rw [show p=minus (A.society l) (B.society l) from rfl,minus_read, A.top_out,hn,B.top_out] at hx
    have hh (A:Performer G I)(x:Mirror G) : chord A.data L x=(List.map (fun i=>A.data (i.2,fun c=>Θ c i.1) x) l).prod:= by rw [← hT]; simp [chord,List.map_map,Function.comp_def]
    simp_rw [← hh _ _] at hx
    unfold Prism.circle at hx
    rw [MeasureTheory.integral_sub ( (hj A).continuousOn.integrableOn_compact (isCompact_closedBall ..)) ((hj B).continuousOn.integrableOn_compact (isCompact_closedBall ..))] at hx
    exact sub_eq_zero.mp hx
  · rintro t ht; rcases List.mem_append.mp ht with hz|hz; exact A.society_limit l _ hz
    obtain ⟨v,hv,rfl⟩:= List.mem_map.mp hz; rw [hn]; exact B.society_limit l v hv

end YM.RG11.Rigidity
