import YM.MS.Graphical.ManyRoot
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.DeepClusters

/-!
# Many-root graphs

At separated positions. `bulk` and `single` will be the schedules sent by the
assembly of the MS-renormalized unmarked and 1-marked graph groups (including
counterterm pages). This construction is on the **punctured z germ**, on the
shifted MS-bar log mass parameter `y`. At each finite set of pins and each
coupling order sum the ways the pins can be joined. In `links`:

* `groupedTree`: bulk in positive perturbative order, absorbed by the pin group
  (at lower order). Single tree bridge (`treeAt`, conserving on the bulk side,
  paying one full shell).
* `touchPair`: two proper nonempty subgroups of pins, right contains the
  anchor (least index). The new line is the loop-type `joinAt` (momentum
  is NOT fixed by conservation), all cross-component allocations as derived
  in `WingLink.lean`. `X.sepCost` is the relative displacement on the left.

These are scale-*forces*. Integrate to the indicated scale, including in the
sum further ordered self-pairs on the joined component with scale lengths after
this one, up to the rank budget (`pinTower`, with padding). See `joined` for
the exact recursion. Disconnected components are NOT included; those go in
`Puff.Mom.bouquet` later.

All edges use the same dimension continuation. External test dimensions may
be arbitrarily high, with no assumption excluding exceptional configurations of
external momenta. At the genuine multi-pin node use UV limit from log-length
−∞ at fixed IR cutoff, with children already MS-renormalized. No change of
subtraction, or rearrangement of order of integration, is assumed. See also
the common-cut results (`Scoreboard.lean`) and coverage (`Audience.lean`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock Rake Geo Latch Job High
open scoped Topology ContDiff Interval
variable {I : Type} [LinearOrder I] {G : Gauge}


namespace Population
variable {m n k : ℕ} {X : Population G I} {s t : Finset I}

lemma urRoom (hp : t∈picks s) (he : Injective X.x) : rootX (fun i (_ :Unit)=> X.x i) t () ≠
    rootX (fun i (_ :Unit)=> X.x i) s () := by
  obtain ⟨h,hv,H,hs⟩ := n_small hp; obtain hu:= hv.mono h.le
  unfold rootX; rw [dif_pos hv,dif_pos hu]; refine he.ne ?_; intro h
  obtain hm := (Finset.mem_filter.mp hp).2.2
  rw [dif_pos hu] at hm
  exact hm (h ▸ Finset.min'_mem t hv)
variable (X)







lemma exactRec {T : Packets G I} : X.closeM T s n =
    pinTower X.y (X.links (X.closeM T s) T s n) (X.budget n s) := by
  unfold closeM; rw [Nat.strongRecOn_eq]; congr 1
  unfold links groupedTree; refine congr_arg₂ (·+·) (Finset.sum_congr rfl (fun i hi=>?_)) rfl
  dsimp only; rw [dif_pos ((Finset.mem_Ico.mp hi).2)]

lemma unpinned : X.clusters ∅ =0:= by funext n; rw [clusters,Finset.strongInductionOn_eq]; simp [recursion]
lemma one (v : I) : X.clusters {v} = X.single v:= by funext n; rw [clusters,Finset.strongInductionOn_eq]; simp [recursion]
lemma joined (hp : 2 ≤ s.card) (n : ℕ) : X.clusters s n=
    pinTower X.y (X.links (X.clusters s) X.clusters s n) (X.budget n s) := by
  let V(t:Finset I):= if t ⊂ s then X.clusters t else 0
  have hx:X.clusters s=X.closeM V s:= by
      funext n; rw [clusters, Finset.strongInductionOn_eq]; simp only [recursion,dif_pos
        (Finset.card_pos.mp (show s.card>0 by omega)),if_neg (show ¬ s.card<2 by omega), dite_eq_ite]; rfl
  rw [hx,X.exactRec]; apply congr_arg (fun T=> pinTower X.y T (X.budget n s)); rw [links,links]; refine congr_arg₂ (·+·) ?_ ?_
  · rfl
  unfold touchPair; exact Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl (fun j _=> by
     simp_rw [V, if_pos (n_small hi|>.1),if_pos (n_small hi|>.2.2.2)])

structure Ready : Prop where
  separated : Injective X.x
  bulkOK n: Countered false (2*n+2 : ℕ) (X.bulk n)
  cost i n: Countered false (X.budget n {i}) (X.single i n)
variable {X}

lemma pairBound (X : Population G I) (hs : t ⊆ s) (h : m+n=k) :
   X.budget m t + X.budget n (s \ t) = X.budget k s:= by
  have hh:= Finset.sum_sdiff hs (f:=X.height); unfold budget; omega

variable (h : Ready X)
include h
section goals
local notation "F" => X.clusters
abbrev Receipt (s : Finset I) (T : ℕ→ Schedule G) (n : ℕ) := Countered false (X.budget n s) (T n)

variable {T : Packets G I} (hp : ∀ i ⊂ s, i.Nonempty→ ∀ j, Receipt (X:=X) i (T i) j)
variable {side : ℕ→Schedule G} (he : ∀ j<n,Countered true (X.budget j s) (side j))

include hp
lemma touches' (hi : t∈picks s) {p : ℕ × ℕ} (hj : p∈antidiagonal n) :
 Countered true (X.budget n s) (joinAt (X.sepCost s t) X.y (T t p.1) (T (s\t) p.2)) := by
  obtain ⟨ht,hv,hs,hL⟩:= n_small hi
  obtain HR := Countered.joinT (hp t ht hv p.1) (hp (s\t) hL hs p.2) (X.sepCost s t) (sub_ne_zero.mpr (urRoom hi h.separated)) X.y
  apply HR.up; obtain hu:= X.pairBound ht.le (Finset.mem_antidiagonal.mp hj);
  omega

omit hp
include he
omit [LinearOrder I] in
lemma tree_link (hi : m ∈ Domain.paths n 0) : Countered true (X.budget n s) (treeAt (X.bulk (n-m)) (side m)) := by
  have hk:= Finset.mem_Ico.mp hi |>.2
  apply ((h.bulkOK (n-m)).treeT (he _ hk)).up; unfold budget; omega

include hp
lemma links_receipt : Countered true (X.budget n s) (X.links side T s n) := by
  apply (Countered.add _ (Countered.sum _ fun t ht=> Countered.sum _ fun v hv=> touches' h hp ht hv)); exact
    Countered.sum _ fun m hm=> tree_link h he hm

omit hp he
lemma formed : Countered (decide (2≤ s.card)) (X.budget n s) (X.clusters s n) := by
  classical
  induction s using Finset.strongInductionOn generalizing n with
  | _ s ih=>
     by_cases hs:2≤s.card; swap
     · obtain he|he:= s.eq_empty_or_nonempty; · subst s; rw [X.unpinned]; exact Countered.zero' ..
       obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from (by obtain he := Finset.card_pos.mpr he; omega));
       rw [decide_eq_false hs, X.one]; exact h.cost _ _
     rw [decide_eq_true hs];
     induction n using Nat.strong_induction_on with
     | h n ht=> rw [X.joined hs]; exact (links_receipt h (fun i hi _ j=> Countered.weak (ih i hi)) ht).poses X.y _

-- UV cost for the *actual* regulated forest input
lemma multi_force_ok (hs : 2≤s.card) (n : ℕ) :
    Countered true (X.budget n s) (X.links (F s) F s n):=
  links_receipt h (fun _ _ _ _=> Countered.weak (formed h)) (fun _ _=> decide_eq_true hs ▸ formed h)

def physicalGroups (T : Packets G I) : Rake.Dance G Unit I:= fun i j=> at4 (T i j)

local notation "μ" => fun _ : Unit => Osc.Snap.planeF
local notation "U" => constantP G Unit (PlanetD G)

include hp he
lemma billed_links : at4 (X.links side T s n) =
    multi μ X.points U U (at4 ∘ X.bulk) (at4 ∘ side) (physicalGroups T) n s := by
  have Hx (i : ℕ) (hi : i∈ Domain.paths n 0) := tree_link h he hi
  have hr (t : Finset I) (ht : t∈ picks s) : Countered true (X.budget n s) (X.touchPair T s t n):=
       Countered.sum _ fun v hv=> touches' h hp ht hv
  rw [links,at4_add (Countered.sum _ Hx) (Countered.sum _ hr)]
  rw [at4_sum _ _ Hx,at4_sum _ _ hr]; unfold multi lonely; refine congr_arg₂ (·+·)
    (Finset.sum_congr rfl fun i hi=>?_) (Finset.sum_congr rfl fun t ht=>?_)
  · funext u s; unfold at4;
    rw [tree_payment (h.bulkOK _) (he _ (Finset.mem_Ico.mp hi|>.2)),bridging_eq]; rfl
  unfold touchPair; rw [at4_sum _ _ (fun i hi=> touches' h hp ht hi)]
  refine Finset.sum_congr rfl fun i hi=>?_ ; funext u v;
  obtain ⟨ht,h',hs,he⟩:= n_small ht; have hS:= hp _ ht h' i.1; have hg:=hp _ he hs i.2
  unfold at4; rw [join_payment hS hg _ (sub_ne_zero.mpr (urRoom ?_ h.separated)), joins_after_specialization _ _ _ (hS.foot _).2 (hg.foot _).2];
  · cases u; rfl
  assumption

omit hp he
lemma groups : Fields X.points μ U U (at4 ∘ X.bulk) (fun i=> at4 ∘ X.single i) (physicalGroups F):= by
  refine ⟨ ?_,fun i=>?_,fun s hs n=>?_⟩
  · funext i; exact (show physicalGroups F ∅ i=0 from (by unfold physicalGroups; rw [X.unpinned,Pi.zero_apply,at4_zero]))
  · funext n; unfold physicalGroups; rw [X.one]; rfl
  rw [show physicalGroups F s=at4 ∘ F s from rfl,← billed_links (s:=s) h (T:=F) (fun i _ _ _=>Countered.weak (formed h)) (side:= F s)
       (fun _ _=> decide_eq_true hs ▸ formed h)]; rw [Function.comp_apply,X.joined hs n]
  exact integrate_every_edge (multi_force_ok h hs n) X.y
end goals
end Population
end YM.MS.Graphical
