import YM.FormalBulk08.Vale.Rill
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {σ η:ℝ}{x:Biglot V}{P Q:Tile (Biglot V) r}{T U:(n: Side)→Tile (Tor n V) r}
-- Profile currency. RELATIVE width charged at x. helpers existence rather than common agreement across ≤all e

def WavePath (o:Biglot V)(A:Tile (Biglot V) r)(T:(n:Side)→Tile (Tor n V) r):Prop:=∃ η:ℝ,0<η ∧ Kalm η o A T
lemma kalm_tighter (h:Kalm η x P T)(hp:σ≤η):Kalm σ x P T:=by obtain ⟨h,C,c⟩:=h; exact ⟨h,C,c.mono (fun j hj=>penn_shrink hj hp)⟩
lemma WavePath.agree (p:WavePath x P T)(h:WavePath x Q T): P=Q:= by ext1 v; obtain ⟨s,hs,p⟩:=p; obtain ⟨t,ht,h⟩:=h; exact tendsto_nhds_unique (p.1 v) (h.1 v)
lemma WavePath.plus (p:WavePath x P T)(h:WavePath x Q U):WavePath x (P+Q) (fun n=>T n+U n):= by obtain ⟨s,hs,p⟩:=p;obtain ⟨t,ht,h⟩:=h; exact ⟨_,lt_min hs ht,(kalm_tighter p (min_le_left ..)).add (kalm_tighter h (min_le_right ..))⟩
lemma WavePath.money (p: WavePath x P T)(c:ℝ): WavePath x (c • P) (fun n=>c • T n):= by obtain ⟨s,hs,p⟩:=p;exact ⟨s,hs,p.smul c⟩
lemma WavePath.dust (p:WavePath x P T)(h:WavePath x Q U):WavePath x (P-Q) (fun n=> T n-U n):= by simp_rw [sub_eq_add_neg]; exact p.plus (by simpa only [neg_one_smul] using h.money (-1))
lemma WavePath.candor (p:WavePath x P T)(e:r=m): WavePath x (lengthen e (sand P)) (fun i=>lengthen e (sand (T i))):= by obtain ⟨s,hs,p⟩:=p;exact ⟨s,hs,p.polish.larger e⟩
lemma wave_empty (x: Biglot V)(r:ℕ): WavePath x (0:Tile _ r) (fun _=>0):= ⟨1,one_pos,fun _=> tendsto_const_nhds,0,.of_forall fun _=>Knox_zeros _⟩
lemma wave_many {P:I→Tile (Biglot V) r}{Q: I→ (n:Side)→Tile (Tor n V) r}(T:Finset I)(h:∀ i∈T,WavePath x (P i) (Q i)): WavePath x (∑ i∈T,P i) (fun n=> ∑ i∈T,Q i n):=by
   induction T using Finset.induction with
   | empty=> simp_rw [Finset.sum_empty]; exact wave_empty _ _
   | @insert i S ht ih=>simp_rw [Finset.sum_insert ht];exact (h i (Finset.mem_insert_self ..)).plus (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma WavePath.clasp {T':Tile (Biglot V) m}{Q:(n:Side)→Tile (Tor n V) m}(p: WavePath x T' Q)(h:WavePath x P T): WavePath x (clutch T' P) (fun n=> clutch (Q n) (T n)) := by
   obtain ⟨s,hs,hp⟩:=p; obtain ⟨t,ht,h⟩:=h;obtain ⟨p,C,H⟩:=kalm_tighter hp (min_le_left s t); obtain ⟨h,A,W⟩:=kalm_tighter h (min_le_right s t); exact ⟨_,lt_min hs ht,fun v=>(p _).mul (h _),_, (H.and W).mono fun j hj=>clasp_cash hj.1 hj.2 (lt_min hs ht).le⟩
lemma flare_leaves {P Q: OrbitV (Biglot V)}{U T:(n:Side)→OrbitV (Tor n V)}(e r:ℕ)(h:∀ i≤e,∀ r,WavePath x (P i r) (fun n=>U n i r))(hp:∀ i≤e,∀ r, WavePath x (Q i r) (fun n=> T n i r)): WavePath x (duplexB P Q e r) (fun n=>duplexB (U n) (T n) e r):= by
   apply wave_many _; intro i hi; apply wave_many _; intro j _; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hi
   exact WavePath.candor ((h _ (by omega) j.val.1).clasp (hp i.2 (by omega) j.val.2)) _ -- arity implicit
lemma deployed {P Q:Waves (Biglot V)}{U T:(n:Side)→Waves (Tor n V)}(n e r:ℕ)(h:∀ j k i, WavePath x (P j k i) (fun n=>U n j k i))(hp:∀ j k i,WavePath x (Q j k i) (fun n=> T n j k i)): WavePath x (doubled P Q n e r) (fun m=>doubled (U m) (T m) n e r):= by
    unfold doubled; apply wave_many _; intro z hz; exact flare_leaves e r (fun _ _ k=>h z.1 _ _) (fun _ _ k=>hp z.2 _ _) -- use 1
lemma wave_cons (x:Biglot V) (e r): WavePath x (bead _ e r) (fun _=>bead _ e r):= by
   by_cases h:e+r=0
   · obtain rfl:r=0:= (by omega); obtain rfl:e=0:=(by omega); refine ⟨1,one_pos,(fun _=> tendsto_const_nhds),1, .of_forall (fun n=>⟨zero_le_one,?_⟩)⟩; simp [Gorge.shine,wide,bead, Reach.self]
   simp_rw [show bead _ e r=(0:Tile (Biglot V) r) from funext (fun _=> if_neg h), show ∀ n:Side,bead _ e r=(0:Tile (Tor n V) r) from fun n=>funext (fun _=> if_neg h)]; exact wave_empty ..
lemma flaring {P:I→OrbitV (Biglot V)}{Q:I→(n:Side)→OrbitV (Tor n V)}(L: List I)(e r)(h:∀ i∈L,∀ j k,WavePath x (P i j k) (fun n=>Q i n j k)): WavePath x (packV P L e r) (fun n=>packV (fun i=>Q i n) L e r):= by
   induction L generalizing e r with
   | nil=> exact wave_cons x e r
   | cons i l ih=>exact flare_leaves e r (fun _ _ _=> h i List.mem_cons_self _ _) (fun j _ k=> ih j k (fun i hi=> h i (List.mem_cons_of_mem _ hi)))
lemma cuffs {P:I→ Waves (Biglot V)}{Q:I→(n:Side)→Waves (Tor n V)} (L: List I)(h:∀ i∈L,∀ j k l,WavePath x (P i j k l) (fun n=>Q i n j k l))(j e r): WavePath x (campfire P L j e r) (fun n=>campfire (fun i=> Q i n) L j e r):= by
   induction L generalizing j e r with
   | nil=> simp_rw [campfire,pebbleW];by_cases he:j=0
           · simp_rw [if_pos he];exact wave_cons x e r
           simp_rw [if_neg he];exact wave_empty x r
   | cons i L ih=>exact deployed (U:=Q i) (T:=fun n=>campfire (fun i=> Q i n) L) j e r (h i List.mem_cons_self) (fun j e r=> ih (fun k hk=>h k (List.mem_cons_of_mem _ hk)) j e r)
end YM.FormalBulk08.Vale
