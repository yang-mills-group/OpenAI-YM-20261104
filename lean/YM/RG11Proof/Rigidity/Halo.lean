import YM.RG11Proof.Rigidity.Arctic

/-!
# Blind to split probes at all distinct real configurations
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free Filter Set Function
open scoped BigOperators Classical
open Crowd
variable {G : Gauge}

-- Auxiliary packet of Bs
def Lamps : Finset E4 → List Panel → Prop
  | _,[]=> True
  | S,P::l=> P.1.2=P.2.2 ∧ P.1.2∉S ∧ Lamps (insert P.1.2 S) l

def Blind (S : Finset E4) (W : Crowd G) : Prop := W.Live S ∧
    ∀ L : List Panel, Lamps S L → (run L W).asks meter=0

namespace Blind
variable {W : Crowd G} {S S' : Finset E4}
lemma addPanel (H : Blind S W) (a b : Foil) {y : E4} (hy : y∉ S) : Blind (insert y S) (panel W (same y a b)) := by
  refine ⟨panelLive (H.1.mono (Finset.subset_insert ..)) (Finset.mem_insert_self y S) (Finset.mem_insert_self y S),?_⟩
  intro L h; exact H.2 (_::L) ⟨rfl,hy,h⟩

lemma chill (H : Blind S W) : Chill S W :=
  ⟨H.1,H.2 [] trivial,fun a b c y z he hy hz=> H.2 [same z b c,same y a a] ⟨rfl,hz,rfl,by simpa [same,he], trivial⟩⟩


lemma Lamps.shift {l : List Panel} (h : Lamps S' l) {S : Finset E4} (hp : S⊆S') : Lamps S l := by
  induction l generalizing S S' with
  | nil => trivial
  | cons i l ih =>
    exact ⟨h.1, fun hi=>h.2.1 (hp hi), ih h.2.2 (Finset.insert_subset_insert _ hp)⟩

lemma extendsQuietly (W T : Crowd G) (h : ∀ q : Word G→ℝ, (∀ {L t},List.Perm L t → q L=q t) → W.asks q=T.asks q)
    (L : List Panel) (q : Word G→ℝ) (hq : ∀ {l t},List.Perm l t → q l=q t) : (run L W).asks q=(run L T).asks q := by
  induction L generalizing W T with
  | nil => exact h q hq
  | cons i l ih =>
    refine ih (panel W i) (panel T i) (fun f hf=> ?_)
    rw [panelRead,panelRead]
    refine Finset.sum_congr rfl fun j _=> h _ fun hw=> hf (hw.append_left _)

lemma farther (H : Blind S W) (P : Panel) (ha : P.1.2∉S) (hb : P.2.2∉S) :
    Blind (insert P.2.2 (insert P.1.2 S)) (W.panel P) := by
  refine ⟨panelLive (H.1.mono ((Finset.subset_insert ..).trans (Finset.subset_insert ..))) (Finset.mem_insert_of_mem (Finset.mem_insert_self ..)) (Finset.mem_insert_self ..),fun L h=> ?_⟩
  induction L generalizing S W with
  | nil => exact H.chill.biloc ha hb P.1.1 P.2.1
  | cons a l ih =>
    rcases a with ⟨⟨i,x⟩,j,y⟩
    have he : x=y := h.1; subst y
    have hk : x∉insert P.2.2 (insert P.1.2 S) := h.2.1
    have hx : x≠P.2.2 ∧ x≠P.1.2 ∧ x∉S := by simpa using hk
    apply Eq.trans (extendsQuietly (W.panel P|>.panel (same x i j)) (W.panel (same x i j)|>.panel P)
      (fun q=> askCommute W q P _) l meter meter_perm)
    apply ih (addPanel H i j hx.2.2) (by simpa using And.intro (Ne.symm hx.2.1) ha) (by simpa using And.intro (Ne.symm hx.1) hb)
    convert! h.2.2 using 1; ext t; simp [or_left_comm]
end Blind

-- Every biloc now uses two independent points, not repeated across the list.
-- (Although the method actually works partially coalesced!)
def Walks : Finset E4 → List Panel → Prop
  | _,[]=> True
  | S,P::l=> P.1.2 ≠ P.2.2 ∧ P.1.2 ∉ S ∧ P.2.2 ∉ S ∧ Walks (insert P.2.2 (insert P.1.2 S)) l

lemma showBlind {S : Finset E4} {W : Crowd G} (h : Blind S W) (L : List Panel) (hl : Walks S L) :
    (run L W).asks meter=0 := by
  induction L generalizing S W with
  | nil => exact h.chill.2.1
  | cons a l ih => exact ih (h.farther a hl.2.1 hl.2.2.1) hl.2.2.2
end YM.RG11.Rigidity
