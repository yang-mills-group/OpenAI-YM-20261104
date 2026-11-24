import YM.XSpace.Stations
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Depth
/-! # Preservation of correlations with auxiliary B implies actual color orbit equality -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial OJoint
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G : Gauge} {d n:ℕ}

abbrev HFields (G:Gauge)(d:ℕ):= ↥(shellSector G d)

def records (G:Gauge)(d:ℕ): HFields G d→ₗ[ℂ] Chamber G d where
  toFun p:= (modal p).choose
  map_add' p q:= by apply appears_inj; rw [map_add,(modal p).choose_spec,(modal q).choose_spec,(modal (p+q)).choose_spec];rfl
  map_smul' t p:= by apply appears_inj; rw [_root_.map_smul,(modal p).choose_spec,(modal (t • p)).choose_spec]; rfl

lemma opensR (p:HFields G d): appears G d (records G d p)=p.val:= (modal p).choose_spec

def negating (p:HFields G d) : HFields G d:= ⟨realForm p.val,(closed_sector p.property 1).2⟩ -- inspect

-- uniform across horizon d. H fixes all elementary undifferentiated quadratics

def postedTeam (H:4≤d)(p q:Flavor 0):HFields G d:= ⟨team G p q,team_label p q H⟩

structure Deliver (H:4≤d)(T:HFields G d→ HFields G d):Prop where
  fixed (p:Flavor 0): T (postedTeam H p p)=postedTeam H p p
  negative p : T (negating p)=negating (T p)
  corpus (n:ℕ)(x:Points n)(v: Fin n→ HFields G d):x∈ conf n→Wick.moment G x (fun i=>(T (v i)).val)= Wick.moment G x (fun i=>(v i).val)

variable {T:HFields G d→ HFields G d}{H:4≤d}
lemma append_room (x:Points n)(h:x∈conf n)(z:E4)(ht:z∉emitters x): Points.cons z x∈conf (n+1):= by
  have he i :z≠x i:= fun hz=> ht (hz ▸ allt ..)
  intro i; refine Fin.cases ?_ (fun j=>?_) i
  · intro b; refine Fin.cases ?_ (fun k=>?_) b
    · simp
    exact fun h=> (he k h).elim
  intro b; refine Fin.cases ?_ (fun k=>?_) b
  · exact fun h=> (he j h.symm).elim
  intro hs; exact congr_arg _ (h (show x j=x k from hs))
lemma append_points (x:Points n)(p:E4): emitters (Points.cons p x)=insert p (emitters x) := by
  ext i; constructor
  · intro hi; obtain ⟨m,h,rfl⟩:= Finset.mem_image.mp hi; refine Fin.cases ?_ (fun i=>?_) m
    · exact Finset.mem_insert_self ..
    exact Finset.mem_insert_of_mem (allt x i)
  intro h; rcases Finset.mem_insert.mp h with h|h
  · subst i; exact (allt (Points.cons p x) 0)
  obtain ⟨j,w,rfl⟩:= Finset.mem_image.mp h; exact (allt (Points.cons p x) j.succ)

def recording (v: Fin n→HFields G d): Mark G n d:= ∏ i, rename (fun k: Voice d×G.ColorIndex=> ((i,k.1),k.2)) (records G d (v i))

lemma transcription (v: Fin n→ HFields G d) (x:Points n): score x G d (recording v)=∏ i, post (x i) (v i).val:= by
  unfold recording; rw [map_prod]; refine Finset.prod_congr rfl fun i h=>?_ ; rw [← opensR (v i)] -- inspect
  apply DFunLike.congr_fun (f:=(score x G d).comp (rename (fun k: Voice d×G.ColorIndex=> ((i,k.1),k.2)))) (g:=(post (x i)).comp (appears G d)); ext1 k; simp only [AlgHom.comp_apply, rename_X, score_one, appears,aeval_X]; rfl

lemma Deliver.since (h:Deliver H T)(v:Fin n→HFields G d)(x:Points n)(hx:x∈conf n) : Silent (emitters x) (score x G d (recording (T ∘ v)-recording v)) := by
  refine ⟨score_keeps x _,fun p hp=>?_⟩
  generalize he : emitters x=B at hp
  induction hp generalizing n with
  | one=> rw [one_mul, _root_.map_sub (score ..), _root_.map_sub,transcription,transcription, ← readings x hx, ← readings x hx]; exact sub_eq_zero.mpr (h.corpus n x v hx)
  | cons H' u hS ih=>
    rename_i S Q z
    rw [← he] at H'
    let f:= postedTeam (G:=G) H u u; let w:= Fin.cons (α:=fun _:Fin (n+1)=> HFields G d) f v
    have ht : T f=f:=h.fixed u
    have hv:= ih w (Points.cons z x) (append_room x hx z H') (by rw [append_points,he]) -- order inspect
    have he (u:HFields G d)(v:Fin n→HFields G d)(w:Fin (n+1) → HFields G d)(h : w=Fin.cons u v): score (Points.cons z x) G d (recording w)= post z u.val*score x G d (recording v):= by
      rw [h,transcription,Fin.prod_univ_succ,transcription]; rfl
    rw [_root_.map_sub (score ..), he f _ w rfl, he f (T ∘ v) _ (by funext i; refine Fin.cases ?_ (fun j=>?_) i; exact ht; rfl),← mul_sub] at hv
    rw [_root_.map_sub (score ..), show post z (team G u u) * Q= Q*post z f.val from mul_comm ..,mul_assoc]; exact hv

variable (K:HFields G d→ HFields G d)
abbrev View (G:Gauge)(d:ℕ):= VectorA (Voice d × G.ColorIndex)

def displayAct (u: HFields G d) (g:View G d)(s:O G.ColorIndex) := watches (changing s (records G d (K u))) g
lemma display_spin (p:HFields G d) (Q:View G d)(s:O G.ColorIndex): displayAct K p Q s=watches (records G d (K p)) (swept s Q):= by unfold displayAct; rw [changing_value]
lemma display_alive (p:HFields G d)(Q: View G d): Continuous (displayAct K p Q) := (evoke_out (records G d (K p)) (MvPolynomial.aeval (fun i=> (↑(Q i):ℂ))).toLinearMap).1

def fusion (g:Fin n→ View G d): VectorA (Deck n d × G.ColorIndex):= WithLp.toLp 2 fun z=> g z.1.1 (z.1.2,z.2)
lemma actor_per (g:Fin n→ View G d)(p:Fin n→HFields G d): watches (evoke (recording (K ∘ p))) (fusion g)=∫ s:O G.ColorIndex, ∏ i, displayAct K (p i) (g i) s ∂(prob G.ColorIndex):= by
  rw [evoke_gaze]; apply integral_congr_ae; apply Eventually.of_forall; intro s
  unfold recording watches; dsimp only; rw [map_prod]; refine Finset.prod_congr rfl fun i _=>?_
  rw [display_spin]
  apply DFunLike.congr_fun (f:=(MvPolynomial.aeval _).comp (rename _)); ext1 k; simp only [AlgHom.comp_apply, rename_X,aeval_X]; rfl

lemma even_stage (P:HFields G d)(y:View G d): watches (records G d (negating P)) y=star (watches (records G d P) y):= by obtain ⟨x,rfl⟩:=chord_full y; rw [← appears_read,← appears_read,opensR,opensR]; exact real_eval ..

namespace Deliver
variable (ht:Deliver H T)
include ht in
lemma display_bar (p:HFields G d)(Q:View G d)(s:O G.ColorIndex): displayAct T (negating p) Q s=star (displayAct T p Q s):= by rw [display_spin,display_spin, ht.negative, even_stage]

include ht
lemma fairs (c:G.ColorIndex) (p:Fin n→ HFields G d)(g:Fin n→ View G d): (∫ s:O G.ColorIndex, ∏ i, displayAct T (p i) (g i) s ∂(prob G.ColorIndex))=∫ s:O G.ColorIndex, ∏ i, displayAct (fun x=>x) (p i) (g i) s ∂(prob G.ColorIndex):= by
  let X (a:Fin n) := (↑a.val:ℝ) • basis 0
  have hx : points X∈conf n:= by intro i j (h:X i=X j); apply Fin.ext; replace h:= smul_left_injective ℝ (m:=basis 0) (by simp [basis]) h; exact_mod_cast h
  have he:= taken (points X) hx c _ (ht.since p (points X) hx)
  rw [show evoke _= evokes (Deck n d) G.ColorIndex (recording (T ∘ p)-recording p) from rfl, _root_.map_sub,sub_eq_zero] at he
  rw [← actor_per T,← actor_per]; exact congr_arg (fun p:Mark G n d=> watches p (fusion g)) he
end Deliver
end YM.XSpace.Stab
