import YM.RG11Proof.Rigidity.Comet

/-!
# All spherical pairings on the deficit
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd Function
open scoped BigOperators Topology Classical

variable {G : Gauge} {P : Type*} [Fintype P]

def weightF (p : Pig G) := 2+p.dart.degree
def cargo (L : Word G) := (L.map weightF).sum
lemma cargo_step (a : Pig G) (L : Word G) : cargo (a::L)=weightF a+cargo L := by simp [cargo]
lemma cargo_pick (L : Word G) (i : Fin (List.length L)) : cargo L = weightF (L.get i)+cargo (L.eraseIdx i.val) := by
  have ht : (L.get i :: L.eraseIdx i.val).Perm L := by simpa using List.getElem_cons_eraseIdx_perm (l:= L) i.isLt
  rw [← cargo_step]; exact ((ht.map weightF).sum_eq).symm

def spool (Θ : P→Stream) (k : P) : Spindle G :=
    (conduit (Θ k),conduit (Θ k))
def mill (Θ : P→Stream) (m : ℕ) (u : List (Pig G→ℝ) → ℝ) : ℝ :=
    loomR Θ m u
where loomR : (P→Stream) → ℕ → (List (Pig G→ℝ) → ℝ) → ℝ
      |_,0,u=>u []
      |Θ,m+1,u=>∑ k:P, ∑ s:G.ColorIndex, loomR Θ m (fun l=> u ((spool Θ k).1 s :: (spool Θ k).2 s :: l))
lemma mill_zero (Θ : P→ Stream) (u : List (Pig G→ℝ) →ℝ) : mill Θ 0 u=u [] := rfl
lemma mill_step (Θ : P→Stream) (u : List (Pig G→ℝ)→ℝ) m :
    mill Θ (m+1) u=∑ k:P,∑ c:G.ColorIndex,mill Θ m (fun l=> u (conduit (Θ k) c :: conduit (Θ k) c :: l)):=rfl
lemma mill_add (Θ:P→Stream) (m : ℕ) (u v : List (Pig G→ℝ)→ℝ) : mill Θ m (fun L=> u L+v L)=mill Θ m u + mill Θ m v := by
  induction m generalizing u v with
  | zero=> rfl
  | succ m h=> simp_rw [mill_step,h,Finset.sum_add_distrib]
lemma mill_mul (Θ:P→Stream) (m : ℕ) (u : List (Pig G→ℝ)→ℝ) (c : ℝ) : mill Θ m (fun L=> c*u L)= c*mill Θ m u := by
  induction m generalizing u with
  | zero=> rfl
  | succ m h=> simp_rw [mill_step,h,Finset.mul_sum]
lemma mill_sum (Θ:P→Stream) (m : ℕ) {I : Type*}(s : Finset I) (u : I→List (Pig G→ℝ)→ℝ) :
    mill Θ m (fun r=>∑ i∈s,u i r)=∑ i∈s,mill Θ m (u i) := by
  induction m generalizing u with
  | zero=> rfl
  | succ m h=> simp_rw [mill_step,h]; rw [Finset.sum_comm (s:=s)]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm

lemma mill_funds (Θ : P→Stream) (u : List (Pig G→ℝ)→ℝ)
    (h : ∀ L : List P, palette (L.map (spool Θ)) u=0) (m : ℕ) : mill Θ m u=0 := by
  induction m generalizing u with
  | zero=> exact h []
  | succ m ih=>
    rw [mill_step]; apply Finset.sum_eq_zero; intro i _
    rw [← mill_sum]; refine ih _ (fun L=> ?_)
    have he:=h (i::L)
    rw [List.map_cons,palette.cons _ _ u] at he; unfold spool at he
    rw [palette.sum]; exact he

lemma sum_wheels (W : Crowd G) (Θ:P→Stream) (m:ℕ)(f : Word G→List (Pig G→ℝ)→ℝ) :
    mill Θ m (fun r=> W.asks (fun w=>f w r))=W.asks (fun w=>mill Θ m (f w)) := by
  induction W with
  | nil => exact (show mill Θ m (fun _ : List (Pig G→ℝ)=>0) = 0 from by
      simpa using mill_mul Θ m (fun _ : List (Pig G→ℝ) => 0) 0)
  | cons a L ih => simp_rw [ask_one,mill_add,mill_mul,ih]

def dial (Θ : P → Stream) (a b : Pig G) : ℝ := ∑ k:P,∑ s:G.ColorIndex,conduit (Θ k) s a * conduit (Θ k) s b
lemma dial_sym (Θ : P→Stream) (a b : Pig G) : dial Θ a b=dial Θ b a := by unfold dial; simp_rw [mul_comm]

def sensors (Θ:P→Stream) (m:ℕ) (W : Word G) := mill Θ m (fun l=> stitch l W)
lemma sensors_zero (Θ:P→Stream) (W : Word G) : sensors Θ 0 W=meter W := rfl
lemma sensors_step (Θ:P→Stream) (m:ℕ) (L : Word G) : sensors Θ (m+1) L =
    Strip.nick (dial Θ) (sensors Θ m) L := by
  unfold sensors nick; rw [mill_step]; simp_rw [stitch]
  unfold pulls
  simp_rw [mill_sum,Finset.mul_sum,mill_sum,mill_mul]
  simp_rw [dial,Finset.sum_mul]
  rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (s:=Finset.univ (α:=G.ColorIndex))] -- syntax
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_; rw [Finset.sum_comm (s:=Finset.univ (α:=P))]; simp only [mul_assoc]

end YM.RG11.Rigidity
