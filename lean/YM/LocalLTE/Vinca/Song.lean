import YM.LocalLTE.Vinca.Concert
import YM.MergeProof.Largo
/-! Cantors. True reservations chosen by duties. All from HERE. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vinca
open YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p : ℕ)(A:Hol G) (W : Worth)
local notation "DO"=> fun i=> GaugeDoor (H.rep N p (i+1)) (H.rep N p i)
set_option quotPrecheck false
open MergeProof
variable (R:∀ m:ℕ,m<N→ GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(Z:∀ m:ℕ,m<N→ Gateway F A (H.rep N p (m+1)) (H.S.side m p))
-- Bind actual factory plan at every step.This H m. Need Z can always choose, not just admissible.
structure Depot (m:ℕ) (R:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(x:ℝ)(V:Gateway F A (H.rep N p (m+1)) (H.S.side m p)) (K: Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities): Prop where
    cost: ∃ (u : Set Wing) (T:Heading F) (a b:ℝ), u.Finite ∧ (∀ i:StockTag (H.S.side (m+1) p),u (.gasKey (cart K i))) ∧ Key B H N p m A R V a b x T u ∧ Buys H F W m a b
    honest: SoundDoor (H.levels.clock.op m p) R
    toll:0≤x
    kappa: Real.sqrt (H.levels.clock.forcedAllowance (m+1))≤1
noncomputable def Arranged (m:ℕ) (T:Voice F H p (m+1))(R:Voice F H p m)(X:Gateway F A (H.rep N p (m+1)) (H.S.side m p)) (K: Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities):Prop:= ∃ E:Employ H N p A m T K,R.plays= marksP H N p A m T K X E
lemma sing {u: ℕ→ℝ} {D:∀ m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)} (h : H.Selected)(hB:B.Sound A) (hw : roomCost H.levels W) (hb : Bank W H.levels) (r : ℕ) (hr : r≤N)
    (V : Voice F H p N) (hu : OnTop B H N p A V) (hv: Chorus H N p N V)
    (Z:∀ m:ℕ,m<N→ Gateway F A (H.rep N p (m+1)) (H.S.side m p)) (K:∀ m:ℕ,∀ _h:m<N,Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (calls : ∀ m:ℕ, r ≤ m → ∀ hm:m<N,Depot B H N p A W m (D m hm) (u m) (Z m hm) (K m hm)):
    ∃ M : Extra.Histories.Music F H N p,M.tone N=V ∧ Sung B H N p A W r M ∧ ∀ m:ℕ,r ≤ m → ∀ hm:m<N, Carol B H N p m (D m hm) (M.tone (m+1)) (M.tone m) (u m) ∧ Arranged H N p A m (M.tone (m+1)) (M.tone m) (Z m hm) (K m hm) ∧ Chorus H N p m (M.tone m):=by
   classical
   induction hr using Nat.decreasingInduction with
   | self=>
     let a (m : ℕ) : Voice F H p m := ⟨fun _ => Extra.Histories.primary 0 0, fun _ => 0,LinearEquiv.refl ℂ _⟩
     let M : Extra.Histories.Music F H N p := ⟨update a N V⟩
     have he : M.tone N=V := update_self N V a
     refine ⟨M,he,⟨he.symm ▸ hu, le_rfl, fun i hi ht => ?_, fun i hi ht => by omega⟩,fun i hi ht=> by omega⟩
     obtain rfl : i=N := le_antisymm ht hi
     rw [he]; exact hu.heard
   | of_succ k hk ih=>
     obtain ⟨M,hM,hS,hD⟩:=ih fun i hi=> calls i (by omega)
     obtain ⟨⟨W',T,t,b,hW,hx,h₀,h₁⟩,hK,hP,hQ⟩:= calls k le_rfl hk
     have hSq: Chorus H N p (k+1) (M.tone _):=by
        by_cases h:k+1=N
        · rw [h,hM]; exact hv
        exact (hD (k+1) le_rfl (by omega)).2.2
     let T':= M.tone (k+1); let E:= (chairs B H N p A k T' (K k hk) h hk (hS.earned _ le_rfl hk)).some
     obtain ⟨v,hMazz,hV,hT,hX,hY⟩:= anthem B H N p A W k (D k hk) (M.tone _) (K k hk) (Z k hk) E h hk (hS.earned _ le_rfl hk) hw hb T hK W' hP h₀ hW hQ h₁ hx hSq hB (fun U=> (Tour.bright H h N p _ hk U).ne')
     let t : Extra.Histories.Music F H N p := ⟨update M.tone k v⟩
     have hh : t.tone k=v := update_self k v M.tone
     have htr (i : ℕ) (hi : k < i) : t.tone i=M.tone i := update_of_ne hi.ne' v M.tone
     refine ⟨t,(htr N hk).trans hM,⟨?_,hk.le, fun i hi he => ?_,fun i hi he => ?_⟩,fun i hi he=>?_⟩
     · rw [htr _ hk]; exact hS.head
     · obtain h|h := lt_or_eq_of_le hi
       · rw [htr _ h]; exact hS.earned i h he
       subst i; rw [hh]; exact hV
     · obtain h|h := lt_or_eq_of_le hi
       · rw [htr i h,htr (i+1) (by omega)]; exact hS.step i h he
       subst i; rw [htr (k+1) k.lt_succ_self,hh]; exact hT
     obtain hl|hl:= lt_or_eq_of_le hi
     · rw [htr i hl,htr (i+1) (by omega)]; exact hD i hl he
     subst i; rw [hh,htr (k+1) k.lt_succ_self]; exact ⟨hY,⟨E,hMazz⟩,hX⟩
end YM.LocalLTE.Vinca
