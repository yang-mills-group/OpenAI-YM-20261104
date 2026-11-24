import YM.XSpace.Mu

/-!
# Wick products supported on the priced books
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Mu
open Lattice Trace Chart2 MvPolynomial Function Set Finsupp Next.Rank.Normal Contraction Outline
open scoped Topology BigOperators
variable {G:Gauge} {d e:ℕ}

lemma inc (p: Word G)(i:Fee G):debt (i::p)=i.cost+debt p:=rfl
lemma surge (p:Word G)(x:Cover): Book G (debt p) (fun _=>story p):=by
  induction p with | nil=>exact Book.unit | cons i p IH=> exact Book.mul (.left i) IH
lemma sound (p:Word G) : Book G (debt p) (fun x=>Trace.volume x (story p)):=by induction p with
  | nil=> simp_rw [steam,map_one]; exact Book.unit
  | cons i p IH => simp_rw [read_word, map_mul,rings]; exact Book.mul (.right i) IH
def holes : Word G → List (Fee G × Word G)
| []=> []
| h::p=> (h,p)::((holes p).map (fun u=> (u.1,h::u.2)))
lemma holes_debt {p:Word G}{i:Fee G×Word G}(h:i∈holes p): debt i.2+i.1.cost=debt p :=by
  induction p generalizing i with
  | nil=> simp [holes] at h
  | cons k p IH=> rw [inc,holes] at *; simp only [List.mem_cons,List.mem_map] at h; rcases h with h|⟨y,hy,rfl⟩; rw [h]; exact add_comm ..; dsimp only; rw [inc,Nat.add_assoc,IH hy]
lemma derivative_steps (x:Cover)(p:Word G)(u:Line G): D (bake u) (Trace.volume x (story p))=
    ((holes p).map (fun i=> (handshake (displace x i.1.line) u:ℂ) • Trace.volume x (story i.2))).sum := by
  induction p with
  | nil=>simp [holes]
  | cons i p ih=> rw [read_word,holes,map_mul (Trace.volume x), rings, (D (bake u)).leibniz,ih, List.map_cons, List.sum_cons, played]; simp only [smul_eq_mul, List.map_map,comp_def, read_word,map_mul,rings,handshake]; rw [mul_comm ((volume x) (story p)), C_mul',add_comm]; congr 1; rw [← List.sum_map_mul_left]; simp [mul_smul_comm]
lemma bookings {I:Type*}{f:I→Tile G}(w:List I)(H:∀ i∈w,f i∈ books G d): (fun x=> (w.map fun i=> f i x).sum)∈books G d:= by
  induction w with
  | nil=> exact Submodule.zero_mem _
  | cons i p IH=> simp_rw [List.map_cons,List.sum_cons]; exact (books _ _).add_mem (H _ (by simp)) (IH fun j hj=> H j (by simp [hj]))
lemma purchase (p q:Word G): Book G (debt p+debt q) (fun x=> tie G (story p) (Trace.volume x (story q))):=by
  induction p generalizing q with
  | nil=>simp only [debt,List.map_nil,List.sum_nil, zero_add,steam,one_tie]; exact sound q
  | cons i p IH=>
    simp_rw [inc,read_word,cross_rule,derivative_steps]; refine Book.add ?_ ?_
    · rw [Nat.add_assoc]; exact Book.mul (.left i) (IH q)
    change (fun x=> _) ∈ books G _; simp_rw [map_list_sum, List.map_map]; apply bookings; intro j hj
    set L:= i.line; let f x:= (handshake (displace x j.1.line) L:ℂ)
    have he x: (tie G (story p) (f x • Trace.volume x (story j.2)))=C (f x)*(tie G (story p) (Trace.volume x (story j.2))):= by rw [map_smul,C_mul']
    change (fun x=> tie G _ (f x • _))∈ _; simp_rw [he]; change Book _ _ _; rw [← holes_debt hj,show i.cost+debt p+(debt j.2+j.1.cost)=(i.cost+j.1.cost)+(debt p+debt j.2) by omega]; exact Book.mul (.rent i j.1) (IH j.2)
lemma productKeen (h:Line G→Prop){p q:Stamp G}(a:p∈Keen h d)(b:q∈Keen h e): p*q∈Keen h (d+e):=by
  induction a using Submodule.span_induction with
  | mem v ht=> obtain ⟨x,hx,rfl⟩:=ht; induction b using Submodule.span_induction with
               | mem v ht=> obtain ⟨y,hy,rfl⟩:=ht; rw [show story x * story y=story (x++y) by simp [story], ← hx.1, ← hy.1, show debt x+debt y=debt (x++y) by simp [debt]]; exact read_hard _ _ fun i hi=> (List.mem_append.mp hi).elim (hx.2 i) (hy.2 i)
               | zero=> rw [mul_zero]; exact Submodule.zero_mem _
               | add a b _ _ i j=> rw [mul_add]; exact Submodule.add_mem _ i j
               | smul _ _ _ IH=> rw [mul_smul_comm]; exact Submodule.smul_mem _ _ IH
  | zero=> rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ i j=> rw [add_mul]; exact Submodule.add_mem _ i j
  | smul _ _ _ IH=> rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ IH

def bounces (G:Gauge)(p:Stamp G)(q:Stamp G)(x:Cover):= tie G p (Trace.volume x q)
lemma earned {p q:Stamp G}(a:p∈elemental G d)(b:q∈elemental G e): bounces G p q∈books G (d+e):=by
  induction a using Submodule.span_induction with
  | mem v ht=> obtain ⟨x,hx,rfl⟩:=ht; induction b using Submodule.span_induction with
               | mem v ht=> obtain ⟨y,hy,rfl⟩:=ht; rw [← hx.1,← hy.1]; exact purchase x y
               | zero=> rw [show ∀ x,bounces G x 0=0 from fun x=> funext fun i=>by simp [bounces]]; exact Submodule.zero_mem _
               | add a b _ _ i j=> exact (show ∀ x,bounces G x (a+b)=bounces G x a+bounces G x b from fun _=> funext fun _=>by simp [bounces]) _ |>.symm ▸ Submodule.add_mem _ i j
               | smul c a _ IH=> exact (show ∀ x,bounces G x (c • a)=c • bounces G x a from fun _=> funext fun _=>by simp [bounces]) _ |>.symm ▸ Submodule.smul_mem _ _ IH
  | zero=> rw [show bounces G 0 q=0 from funext fun _=>by simp [bounces]]; exact Submodule.zero_mem _
  | add a b _ _ i j=> rw [show bounces G (a+b) q=bounces G a q+bounces G b q from funext fun _=>by simp [bounces]]; exact Submodule.add_mem _ i j
  | smul c a _ IH=> rw [show bounces G (c • a) q=c • bounces G a q from funext fun _=>by simp [bounces]]; exact Submodule.smul_mem _ _ IH
end YM.XSpace.Mu
