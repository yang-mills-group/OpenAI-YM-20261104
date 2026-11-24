import YM.RG11Proof.Rigidity.Sieve

/-!
# Loom of pure cross tests on any announced finite word assembly
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free palette Strip Crowd
open scoped BigOperators Classical

variable {G : Gauge}

abbrev Roll := Pig G → ℝ
/-- Attach all marks across the channel, sum multiplicities of choices. -/
def stitch {G : Gauge} : List (Pig G → ℝ) → Word G → ℝ
  | [],L=>meter L
  | a::p,L=>pulls L (fun b r=> a b * stitch p r)
lemma stitch_perm {u v : List (Pig G→ℝ)} (h : u.Perm v) (L : Word G) : stitch u L=stitch v L := by
  induction h generalizing L with
  | nil=>rfl
  | cons a h ih=> simp_rw [stitch,ih _]
  | swap a b l =>
    unfold stitch stitch; simp_rw [← pulls_mul]
    rw [pulls_twice L (fun i j r=>b i*(a j*stitch l r))]; simp [mul_left_comm]
  | trans h g h1 h2=> exact (h1 L).trans (h2 L)
lemma stitch_quote (u : List (Pig G)) (L : Word G) : stitch (u.map line) L= rate line line u L 0 := by
  induction u generalizing L with
  | nil => rw [rate_nil]; rfl
  | cons a l ih => simp_rw [rate_cons,zero_mul,pulls_zero,zero_add, List.map_cons,stitch,ih _]

lemma palette_map {A B : Type*} (f : A→B) (L : List (Dye G.ColorIndex A)) (μ : List B→ℝ) :
    palette L (fun u=> μ (u.map f))=palette (L.map (fun p=> (f ∘ p.1,f ∘ p.2))) μ := by
  induction L generalizing μ with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons,palette.cons,palette.cons]; simp_rw [List.map_cons]; exact Finset.sum_congr rfl (fun i _=> ih (fun L=> μ (f (a.1 i) :: f (a.2 i) :: L)))

abbrev Spindle (G : Gauge) := Dye G.ColorIndex (Pig G→ℝ)

def stainL (W : Crowd G) (L : List (Spindle G)) := palette L (fun p=> W.asks (stitch p))
def turnPanel (i : Panel) : Spindle G := ((line ∘ hear i.1),(line ∘ hear i.2))
lemma loom {S : Finset E4} {W : Crowd G} (hW : Blind S W) (L : List Panel) (h : Journey Prod.snd S L) :
    stainL W (L.map turnPanel)=0 := by
  have he := blank hW L h 0
  unfold deck at he
  simp_rw [← stitch_quote] at he
  rw [palette_map (G:=G) line (L.map (byColor hear)) (fun p=> W.asks (stitch p)),List.map_map] at he
  exact he

end YM.RG11.Rigidity
