import YM.RG11Proof.Rigidity.Rations

/-!
# Assemblies: real finite linear combinations of words
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Tensor Analysis Maxwell Maxwell.Free Extra.FD.SphereTest Filter Set
open scoped BigOperators Topology ContDiff Classical

abbrev Crowd (G : Gauge) := List (ℝ × Word G)

namespace Crowd
variable {G : Gauge}

def asks (W : Crowd G) (q : Word G → ℝ) := (W.map fun w=> w.1*q w.2).sum
@[simp] lemma ask_zero (q : Word G → ℝ) : asks [] q=0 := rfl
@[simp] lemma ask_one (w : ℝ × Word G) (W : Crowd G) (q : Word G → ℝ) : asks (w::W) q=w.1*q w.2+asks W q := by
  simp [asks]
@[simp] lemma ask_append (W T : Crowd G) (q : Word G → ℝ) : asks (W++T) q=asks W q+asks T q := by simp [asks]
lemma ask_add (W : Crowd G) (q p : Word G → ℝ) : asks W (fun L=>q L+p L)=asks W q+asks W p := by
  induction W with | nil => simp | cons a l h => simp [h,mul_add]; ring
lemma ask_mul (W : Crowd G) (q : Word G → ℝ) (v : ℝ) : asks W (fun L=>v*q L)=v*asks W q := by
  induction W with | nil => simp | cons a l h => simp [h];ring
lemma ask_const_zero (W : Crowd G) : asks W (fun _=>0)=0 := by simp [asks]
lemma ask_sum {I : Type*} (W : Crowd G) (q : I → Word G → ℝ) (s : Finset I) :
    asks W (fun L =>∑ i∈s,q i L) = ∑ i∈s, asks W (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ask_const_zero]
  | insert a s ha ih => simp_rw [Finset.sum_insert ha,ask_add,ih]

def Live (S : Finset E4) (W : Crowd G) : Prop := ∀ w∈W, ∀ i∈ (w.2 : Word G), (i:Pig G).origin ∈ S
lemma Live.mono {S H : Finset E4} {W : Crowd G} (h : Live S W) (ht : S⊆H) : Live H W := fun w hw i hi=> ht (h w hw i hi)

lemma ask_ghost (U : Set E4) {W : Crowd G} (q : Word G → E4 → ℝ)
    (h : ∀ w∈W,Ghost U (q w.2)) : Ghost U (fun x=>asks W (fun L=> q L x)) := by
  induction W with
  | nil => simp; exact Ghost.zeroG
  | cons a l ih =>
    simp only [ask_one]
    simp_rw [mul_comm a.1]
    exact ((h a (List.mem_cons_self ..)).mulG _).addG (ih (fun w hw=>h w (List.mem_cons_of_mem a hw)))

lemma ask_diff {W : Crowd G} (q : Word G → E4 → ℝ) {z : E4}
    (h : ∀ w∈W,ContDiffAt ℝ ω (q w.2) z) : ContDiffAt ℝ ω (fun x=>asks W (fun L=> q L x)) z := by
  induction W with
  | nil => exact contDiffAt_const
  | cons a l ih =>
    simp only [ask_one]; exact (contDiffAt_const.mul (h _ (List.mem_cons_self ..))).add (ih (fun w hw=> h w (List.mem_cons_of_mem a hw)))

-- A quadratic invariant, or a *putative* fixed bilocal (both entries now
-- singles if positions differ).
abbrev Panel := (Foil × E4) × (Foil × E4)
def painting (G : Gauge) (P : Panel) (c : G.ColorIndex) : Word G := [toss P.1.1 P.1.2 c,toss P.2.1 P.2.2 c]
def invite (W : Crowd G) (L : Word G) : Crowd G := W.map (fun t=> (t.1,L++t.2))
def panel (W : Crowd G) (P : Panel) : Crowd G :=
    (Finset.univ : Finset G.ColorIndex).toList.flatMap fun c=> invite W (painting G P c)
lemma invited (W : Crowd G) (L : Word G) (q : Word G → ℝ) : asks (invite W L) q=asks W (fun l=> q (L++l)) := by simp [asks,invite]; rfl

lemma askTickets {I : Type*} (L : List I) (w : I → Crowd G) (q : Word G → ℝ) :
    asks (L.flatMap w) q=(L.map fun i=>asks (w i) q).sum := by
  induction L with
  | nil => rfl
  | cons a l ih => simp [ih]

lemma panelRead (W : Crowd G) (P : Panel) (q : Word G → ℝ) :
    asks (panel W P) q=∑ c : G.ColorIndex, asks W (fun l=> q (painting G P c++l)) := by
  unfold panel; rw [askTickets,Finset.sum_map_toList]; simp_rw [invited]

lemma panelLive {W : Crowd G} {P : Panel} {S : Finset E4} (h : Live S W)
    (h0 : P.1.2∈S) (h1 : P.2.2∈S) : Live S (panel W P) := by
  rintro w hw i hi; obtain ⟨c,hc,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
  rcases List.mem_append.mp hi with he|he; swap; exact h t ht _ he
  simp only [painting,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  · exact h0
  exact h1

def run : List Panel → Crowd G → Crowd G
  | [],W=> W
  | P::L,W=> run L (panel W P)
lemma run_append (L K : List Panel) (W : Crowd G) : run (L++K) W=run K (run L W) := by
  induction L generalizing W with
  | nil => simp [run]
  | cons a l ih => simp [run,ih]

lemma askCommute (W : Crowd G) (q : Word G → ℝ) (P T : Panel)
    (hq : ∀ {l t}, List.Perm l t → q l=q t) : asks ((W.panel P).panel T) q=asks ((W.panel T).panel P) q := by
  simp_rw [panelRead]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  congr 1; funext l; apply hq; simp_rw [← List.append_assoc]; exact (List.perm_append_comm).append_right _
end Crowd
end YM.RG11.Rigidity
