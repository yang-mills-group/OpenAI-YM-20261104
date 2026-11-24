import YM.OPE.Screens.Entry
/-!
# Consume on any Viewers

This part can still see the projected vector components on the unselected filter,
no assumption than the actual sign price. Assembly formulas specialize it to the
unselected readings at the single high-water mark q, and the ancestor mirror.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec Cards
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G: Gauge}
    {k b n m l q u j p N W d e :ℕ} {C: Family G} {c A A' o o' α η:ℝ}
    {F:Extraction.Order} {S:Table C.book}(U:Final C F S) {x:I→ Cover}{v:I→ C.book.Token}
    {Y:J→ E4} {w:J→ C.book.Token}
    {f φ: Filter (ℕ×ℕ)}[f.NeBot] (h:φ ≤ F.fuse)
local notation "Z!"=> C.S.gridPoint k ∘ x
local notation "Ξ!"=> (fun _ : Unit=>(0:E4))
-- Term onC root read. Order of slots convention
abbrev chunk (s:Finset I){Z:Type}(x:I→Z) : (↑s:Type)→Z:= fun i=>x i.val
def substituted (s:Finset I)(X:I→ E4) := beside (sole (0:E4)) (chunk (univ\ s) X)
abbrev negative (X:C.label d) : Unit→ C.book.Token:= fun _=>⟨d,X⟩
def substituted_row {d:ℕ} (s:Finset I)(v:I→ C.book.Token)(x:C.label d):= beside (negative x) (chunk (univ\s) v)
def card_read (U:Table C.book)(x:I→ E4)(v:I→ C.book.Token)(y:J→ E4)(w:J→ C.book.Token):= observe U (beside x y) (beside v w)
abbrev unit_read (U:Table C.book)(x:C.label d):= card_read (C:=C) (J:=J) U (Ξ!) (negative x)
namespace Probe
variable (B:Viewer C F w b c α)(D: Org.Grill C F)(hk:b ≤ k)
    (p q' : Spark C f k)
local notation "fτ"=> (fun t=> Probe.view U t w Y)
-- pure onA view transfer using spark
include U B D in
lemma pairs (hr:f ≤ F.fuse)(e:b ≤ k){o:ℝ}(hp:∀ᶠ i:ℕ×ℕ in f,PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) o ((p.cuts-q'.cuts) i.1 i.2))(hx:Injective (beside (point p) Y)) (hy:Injective (beside (point q') Y))(hY:ClearOf 0 Y c) : ‖fτ p-fτ q'‖ ≤ o*α:=by -- include B D etc
    let a:Fin 2→ℂ:=![1,-1]; let L:Fin 2→ Spark C f k:=![p,q']; have ht : ∀ i,Injective (beside (point (L i)) Y):=by intro i; fin_cases i; exact hx; exact hy
    have hQ:= sold U hr B D a e hp (Eventually.of_forall fun i=> (show (fun V=>∑ j,a j*(L j).cuts i.1 i.2 V)=(p.cuts-q'.cuts) i.1 i.2 from funext fun V=>by simp [a,L,sub_eq_add_neg,Fin.sum_univ_succ])) ht hY; simpa [a,L,Fin.sum_univ_succ,sub_eq_add_neg] using! hQ
lemma readChunk (p:Spark C f k)(hx:Injective (beside (point p) Y))(v:Viewers U)(w:J→ C.book.Token) : glance U v (view U p w Y) =read p (spectator U v) w Y:= glance_sees U _ _ _ hx
lemma card_same (p:I→ C.book.Token)(hp:S.classTokens ∘ p=S.classTokens ∘ v)(hx:Injective (beside (Z!) Y))(s: Viewers U): card_read (C:=C) (spectator U s) Z! p Y w=card_read (C:=C) (spectator U s) Z! v Y w:= by
    unfold card_read; rw [← glance_sees U s _ _ hx,← glance_sees U s _ _ hx]; congr 1; exact mingle U (show S.classTokens ∘ _=S.classTokens ∘ _ from ((beside_commutes p w S.classTokens).trans ((congr_arg (fun x=> beside x _) hp).trans (beside_commutes v w _|>.symm)))) hx
include D B hk
-- specialize subarray sign
variable {V:ReadLabel C v}{z:ℕ×ℕ→ C.label d}{y:C.label d}
lemma first_read (s:Viewers U)(hr:f ≤ F.fuse)(he:∀ᶠ i:ℕ×ℕ in f,PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) A ((lobby x v V k - stampEntry d z) i.1 i.2))
    (hp: Screen Z!)(ht:∀ i,Tendsto (V i) f (𝓝 (v i).2))(hz:Tendsto z f (𝓝 y))
    (hx:Injective (beside (Z!) Y))(hy:Injective (beside (Ξ!) Y))(hY:ClearOf 0 Y c): ‖card_read (C:=C) (spectator U s) Z! v Y w - unit_read (C:=C) (spectator U s) y Y w‖ ≤ A*α:=by
    let p:=seen hp ht; let q':=host hz k; have hX: (fτ p)= viewing U (beside (Z!) Y) (beside v w):= rfl; have hu : (fτ q') = viewing U (beside (Ξ!) Y) (beside (negative y) w):=by unfold view q'; dsimp only; rw [hostPoint]; rfl
    apply le_trans (le_of_eq (congr_arg Norm.norm (show card_read .. - _ = glance U s (fτ p-fτ q') from ?_ ))) ((glance_bound U s (_-_)).trans ?_)
    · rw [hX,hu,map_sub,glance_sees U _ _ _ hx,glance_sees U _ _ _ hy]; rfl
    exact pairs U B D p q' hr hk (by unfold q'; rw [hostcut]; exact he) hx (by unfold q'; rw [hostPoint]; exact hy) hY
include h
lemma root_read (s: Viewers U)(hp:Dir C S k b m d o A x v φ y)
    (hs:Screen Z!)(hx:Injective (beside (Z!) Y))(hy:Injective (beside (Ξ!) Y))(hY:ClearOf 0 Y c): ‖card_read (C:=C) (spectator U s) Z! v Y w - unit_read (C:=C) (spectator U s) y Y w‖ ≤ A*α:= by
    obtain ⟨g,p,V,f,hb,hh,hf,hE,hT⟩:=hp.ready; rw [← card_same U p hf.ongoing hx s]; exact first_read U B D hk s (le_trans hh h) hT hs hf.values hE.wins hx hy hY
omit h
-- helpers.Eq root spelling
lemma triple (p q r:Spark C f k)(h':f ≤ F.fuse)(hp:∀ᶠ i:ℕ×ℕ in f,PaidAt C.S i.1 i.2 b (C.beta i.1 i.2) o ((p.cuts-q.cuts-r.cuts) i.1 i.2)) (hx:Injective (beside (point p) Y))(hy:Injective (beside (point q) Y))(hz:Injective (beside (point r) Y))(hh:ClearOf 0 Y c) : ‖fτ p-fτ q-fτ r‖ ≤ o*α:=by
    let a:Fin 3→ℂ:=![1,-1,-1]; let L:Fin 3→ Spark C f k:= ![p,q,r]; have ht :∃ H:ℕ,H=1:=⟨_,rfl⟩; have hu : ∀ i,Injective (beside (point (L i)) Y):=by intro i;fin_cases i; exact hx; exact hy; exact hz
    have hQ := sold U h' B D a hk hp (Eventually.of_forall fun i=> (show (fun V=> ∑ j,a j*(L j).cuts i.1 i.2 V)=(p.cuts-q.cuts-r.cuts) i.1 i.2 from funext fun V=>by simp [a,L, sub_eq_add_neg,Fin.sum_univ_succ,add_assoc])) hu hh; simpa [a,L,sub_eq_add_neg,Fin.sum_univ_succ,add_assoc] using! hQ
omit D B hk in
lemma seconds {s:Finset I}{Z:Type}{U:I→ Z} (hs:Injective U): Injective (chunk s U):=fun i j h=> Subtype.ext (hs h)
omit D B hk in
lemma pinned {I:Type}[Fintype I][DecidableEq I]{s:Finset I}{x:I→ E4}(hp:Screen x): Screen (chunk s x):=fun i=> seconds (hp i)
omit D B hk in
lemma affiliate {I J:Type}[Fintype I][DecidableEq I][Fintype J]{Z:Type}{x:I→Z}{y:J→Z}{s:Finset I}(h: Injective (beside x y)) : Injective (beside (chunk s x) y):= by
    obtain ⟨h₁,h₂,h₃⟩:= beside_distinct.mp h; exact beside_distinct.mpr ⟨seconds h₁,h₂, fun i j=> h₃ i.val j⟩
include h
local notation "L!"=> (fun s:Finset I=> (chunk s Z!))
local notation "M!"=> (fun s:Finset I=> (substituted s Z!))
end Probe
end YM.OPE.Log.Trunk.Shuttle
