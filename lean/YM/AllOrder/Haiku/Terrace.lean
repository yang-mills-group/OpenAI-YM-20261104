import YM.AllOrder.Haiku.Present
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Coat
open PertExtension.Series Radial
-- finite order k packet row. iterate adding via `∀j < r`
abbrev Theatre (G:Gauge)(ι:Type) := ι→ℕ→Ink.Money.Bills (Coarse G)
abbrev Roster (ι:Type)(G:Gauge)(k:ℕ) := (t:Fin (k+1)) → ι→ Packet G (t.val+2)
def memoir (Λ₀ : ι→ℝ)(F:Theatre G ι)(j:ℕ) := (∀ k ≤ j,∀ i n, Rank (Link G n) (k+2) (F i k n) ∧ Etiquette (F i) n k)∧ (∀ k≤j, ∀ r:ℕ,Ready Λ₀ (fun i=>F i k) r)
variable (Λ₁:ι→ℝ) {F G':Theatre G ι}
lemma Memoir_less (H:memoir Λ₁ F k)(h:memoir Λ₁ G' k): memoir Λ₁ (F-G') k:= by
 refine ⟨fun r hr i n=> ⟨(H.1 r hr i n).1.sub (h.1 r hr i n).1, (H.1 r hr i n).2.less ((h.1 r hr i n).2) (fun j hj=> (H.1 j (hj.trans hr) i n).1.read) (fun j hj=> (h.1 j (hj.trans hr) i n).1.read)⟩,fun r hr j=> ?_⟩; exact ((H.2 r hr j).joint (h.2 r hr j) (fun i n=> (H.1 r hr i n).1.read.smooth.contDiffAt.analyticAt) (fun i n=> (h.1 r hr i n).1.read.smooth.contDiffAt.analyticAt)).1
variable (X:Roster ι G k) (H:∀ j,Curled Λ₁ (X j))
def reel (X:Roster ι G k) (s:Finset (Fin (k+1))) : Theatre G ι := ∑ a∈s,(fun i=> trade k (X a i))
include H
lemma story (s:Finset (Fin (k+1))) (h:memoir Λ₁ F N): memoir Λ₁ (F-reel X s) N := by
 induction s using Finset.induction_on with
 | empty=> simpa only [reel,Finset.sum_empty,sub_zero] using h
 | insert i s ht ih=>
   let f:= fun j:ι=> trade k (X i j); let g:= F-reel X s; have he : F-reel X (insert i s)=g-f:= by unfold g; rw [reel,sum_insert ht]; unfold f reel; abel
   rw [he]; refine Memoir_less _ ih ⟨fun k' hk y n=>?_,fun r hr p=> tradeStory k (H i) r p⟩; obtain ⟨a,ha,F,hg'⟩:= H i; exact ⟨trade_r k k' n (by have := i.isLt; omega), trade_et k ((hg'.2 y).1) ha ((hg'.2 y).2) _ _⟩
abbrev Repertoire (ι:Type)(G:Gauge):= (k:ℕ)→Roster ι G k
variable {H} {Λ₁} {T: Repertoire ι G}
omit H
def crowd (T: Repertoire ι G)(p:ℕ) := ∑ i∈range p, reel (T i) Finset.univ
def strict (F:Theatre G ι)(r:ℕ):Prop := ∀ i n, Station r n (F i)
structure Spliced (Λ₁:ι→ℝ)(F:Theatre G ι) (T:Repertoire ι G) (k:ℕ) : Prop where
 age (v:ℕ): v < k → ∀ i:Fin (v+1), Curled Λ₁ (T v i)
 project : strict (F-crowd T k) k
lemma storyD (H:memoir Λ₁ F N)(h:Spliced Λ₁ F T k): memoir Λ₁ (F-crowd T k) N:= by
  have he (a:ℕ) (ha:a≤k) : memoir Λ₁ (F-crowd T a) N:=by
     induction a with
     | zero=> simpa [crowd] using H
     | succ a ih=> let g:= F-crowd T a; have hh := story Λ₁ (T a) (h.age a (by omega)) univ (ih (by omega)); unfold crowd; rw [Finset.sum_range_succ,sub_add_eq_sub_sub]; exact hh
  exact he k le_rfl
-- advancing induction
lemma lesson (h:memoir Λ₁ F N)(p:ℕ)(hp:p≤N)(H:strict F p) (hG:G.Simple): ∃ X:Roster ι G p, (∀ i,Curled Λ₁ (X i)) ∧ strict (F-reel X univ) (p+1) := by
   have ha(i:ι): Admits (F i p):= votes (fun n=> (h.1 p hp i n).2) (H i) (fun n=> (h.1 p hp i n).1.read); choose X hC hB using (fun k:Fin (p+1)=> palette ha k.val (h.2 p hp (k.val+1))); refine ⟨X,hC,fun i n k hk=>?_⟩; let v:= F i k n; let u:= reel X univ; let G':=v - u i k n;
   rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hK|hK
   · have he : u i k n=0:= by unfold u reel; simp_rw [Finset.sum_apply, trade, if_neg (Nat.not_le_of_lt hK),Finset.sum_const_zero];
     change Constant (v-u i k n); rw [he,sub_zero]; exact H i n k hK
   subst k; have hr:= (h.1 p hp i n).1; have hs := Project.still_one hG ((ha i).color n) ((ha i).rise n)
   have hz(x:Link G n): u i p n x=v x-v 0:= by
      have hh(a: Fin (p+1)): trade p (X a i) p n= jet v (a.val+2):= by simp only [trade,le_refl,if_true,Nat.sub_self,zero_add]; exact (hB ..).symm
      unfold u reel; simp_rw [Finset.sum_apply,hh]; have hd(x:Link G n):jet v 1 x=0:= by unfold jet; change (↑(Nat.factorial 1):ℝ)⁻¹ * iteratedFDeriv ℝ 1 (F i p n) 0 _=0; rw [hs]; simp
      have hx:= Ink.Pointwise.full_span x (f:=v) hr; rw [sum_range_succ',sum_range_succ'] at hx; rw [← Fin.sum_univ_eq_sum_range,hd, jet_zero, add_zero] at hx -- order
      linarith only [hx]
   change Constant G'; intro x y; change v x-u i p n x=v y-u i p n y; rw [hz,hz]; ring
lemma Spliced.up (h:Spliced Λ₁ F T k) (hk:k≤ N) (H:memoir Λ₁ F N)(hG:G.Simple) : ∃ U, Spliced Λ₁ F U (k+1) ∧ ∀ i<k,U i=T i := by
 obtain ⟨X,hX,hu⟩:= lesson (storyD H h) k hk h.project hG; let U:= Function.update T k X; have hv : U k=X:= by unfold U; simp
 have hp( i:ℕ)(h:i<k): U i=T i:= Function.update_of_ne h.ne _ _
 refine ⟨U,⟨?_,?_⟩,hp⟩; · intro i hi; rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h'|h'; exact hp i h' ▸ h.age i h'; exact h' ▸ hv.symm ▸ hX -- maybe rw eq dep Curled Rank
 rw [crowd,Finset.sum_range_succ, hv, show ∑ i∈range k,reel (U i) Finset.univ= _ from (show ∑ i∈range k,reel (U i) Finset.univ=crowd T k from Finset.sum_congr rfl (fun i hi=> (by rw [hp i (Finset.mem_range.mp hi)]))),sub_add_eq_sub_sub]; exact hu

-- fill dummy stage from ANY issued skin. Nonempty construct from instance `Atom` maybe none.
lemma onRamp (H:memoir Λ₁ F N)(hG:G.Simple) : ∃ T,Spliced Λ₁ F T (N+1):= by
 let W : Repertoire ι G:= fun i j v=> issue (G:=G) (t:=j.val+1) 0
 have h(k:ℕ)(hk:k≤ N+1):∃ U,Spliced Λ₁ F U k:= by induction k with
 | zero=> exact ⟨W,⟨fun i hi=> (Nat.not_lt_zero _ hi).elim,fun i n j hj=> (Nat.not_lt_zero _ hj).elim⟩⟩
 | succ i ih=> obtain ⟨U,hU⟩:= ih (by omega); obtain ⟨y,hy,H⟩:= hU.up (by omega) H hG; exact ⟨y,hy⟩
 exact h _ le_rfl
end Coat
end YM.AllOrder.Haiku
