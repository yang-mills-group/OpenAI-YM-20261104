import YM.FormalBulk08.Lotus.Seal

/-! One pulse on bulk and on all periodic simulants. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function Wick
open scoped BigOperators Classical ENNReal Topology
variable {r : ℕ} {I J : Type*} (η : ℝ)

def Kith (T : Tile (Biglot I) r) (S : (n:Side) → Tile (Tor n I) r) := Light T S ∧ ∃ C, Bright S η C
variable {η}
lemma Kith.add {T U : Tile (Biglot I) r} {S M : (n:Side) → Tile (Tor n I) r} (h : Kith η T S) (e : Kith η U M) : Kith η (T+U) (fun n=> S n+M n) := by
   obtain ⟨h,C,H⟩:= h; obtain ⟨e,B,E⟩:=e; exact ⟨fun v=> (h v).add (e v), C+B,(H.and E).mono fun _ hv=> hv.1.add hv.2⟩
lemma Kith.smul {T : Tile (Biglot I) r} {S : (n:Side)→ Tile (Tor n I) r} (h : Kith η T S) (c : ℝ) : Kith η (c • T) (fun n=>c • S n) := by
   obtain ⟨h,C,H⟩:=h; exact ⟨fun v=>(h v).const_mul _,_,H.mono fun _ hn=> hn.smul c⟩
lemma Kith.polish {T : Tile (Biglot I) r} {S : (n:Side)→ Tile (Tor n I) r} (h : Kith η T S) : Kith η (sand T) (fun n=>sand (S n)) := by
   obtain ⟨h,C,H⟩:=h; exact ⟨fun v=> (Tendsto.div_const (tendsto_finsetSum _ (fun j _=>h _)) _),C,H.mono fun _ hn=> hn.smooth⟩ -- comp implicit
lemma Kith.larger {T : Tile (Biglot I) r} {S : (n:Side)→ Tile (Tor n I) r} (h : Kith η T S) {m : ℕ} (e : r=m) : Kith η (lengthen e T) (fun n=>lengthen e (S n)) := by cases e; exact h
lemma kith_many {T : J→Tile (Biglot I) r} {S : J→(n:Side)→ Tile (Tor n I) r} (B : Finset J) (h : ∀ i∈B,Kith η (T i) (S i)) : Kith η (∑ i∈B,T i) (fun n=>∑ i∈B,S i n) := by
   induction B using Finset.induction with
   | empty=> simp only [Finset.sum_empty]; exact ⟨fun _=>tendsto_const_nhds,0,.of_forall fun _=>bail_void _ _ _⟩ -- name expansion
   | @insert a b he ih=> simp_rw [Finset.sum_insert he]; exact (h _ (Finset.mem_insert_self _ _)).add (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))

variable {q : Biglot I→Biglot I→ℝ} {M : (n:Side)→Tor n I→Tor n I→ℝ}
    (e : Wind q M) (C : ℝ) (hs : 0<η) (H : ∀ᶠ n in atTop, Grate (lake n I) η (M n) C) (hh : ∀ n i j, M n i j=M n j i)
variable [Fintype I]
include e H hs
lemma kith_stare {T : Tile (Biglot I) (r+1+1)} {S : (n:Side)→ Tile (Tor n I) (r+1+1)} (i : Fin r) (h : Kith η T S) : Kith η (stare q T) (fun n=>stare (M n) (S n)) := by
   obtain ⟨h,B,hv⟩:=h; exact ⟨sparkle_stare h e B C hs hv H i,_,(H.and hv).mono fun _ hx=> hx.2.stare hs.le hx.1.1 (hx.1.rough hs.le)⟩
include hh
lemma kith_bond {m n : ℕ} {T : Tile (Biglot I) (m+1)} {S : (n':Side)→ Tile (Tor n' I) (m+1)} {R : Tile (Biglot I) (n+1)} {P : (n':Side)→Tile (Tor n' I) (n+1)}
    (v : Fin (m+n)) (h : Kith η T S) (hg : Kith η R P) : Kith η (bond q T R) (fun a=>bond (M a) (S a) (P a)) := by
   obtain ⟨h,B,hv⟩:=h; obtain ⟨e',A,ha⟩:=hg
   exact ⟨sparkle_bond v h e' e B A C hs hv ha H,_,(hv.and (ha.and H)).mono fun n' hw=> hw.1.bond (M n') hs.le hw.2.1 hw.2.2 (hh n')⟩
lemma kith_swim {T : OrbitV (Biglot I)} {S : (n: Side)→OrbitV (Tor n I)} (hx : ∀ b r,0<r → Kith η (T b r) (fun n=>S n b r)) (u k r : ℕ) (hp : 0<r) : Kith η (swim q T u k r) (fun n=>swim (M n) (S n) u k r) := by
   induction u using Nat.strong_induction_on generalizing k r with
   | _ u ih=>
      cases u with
      | zero=> simp_rw [swim_first];exact hx k r hp
      | succ u=>
          simp_rw [swim_succ]; refine Kith.smul (Kith.add (kith_stare e C hs H (⟨0,hp⟩ : Fin r) (ih u (by omega) _ _ (by omega))) ?_) _
          unfold brawl reach; apply kith_many _; intro a _; apply kith_many _; intro b hb; apply kith_many _; intro w _; simp_rw [visor_eq]
          rw [Finset.mem_antidiagonal] at hb; exact ((kith_bond e C hs H hh (⟨0,(Finset.mem_antidiagonal.mp w.property).symm ▸ hp⟩ : Fin (w.val.1+w.val.2)) (ih b.1 (by omega) _ _ (by omega)) (ih b.2 (by omega) _ _ (by omega))).polish).larger _
end YM.FormalBulk08.Lotus
