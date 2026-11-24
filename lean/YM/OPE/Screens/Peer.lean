import YM.OPE.Screens.Summing
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
namespace Probe
variable (B:Viewer C F w b c α) (D: Org.Grill C F) (hk:b ≤ k)
    (p q' : Spark C f k)
local notation "fτ"=> (fun t=> Probe.view U t w Y)
variable {V:ReadLabel C v}{z:ℕ×ℕ→ C.label d}{y:C.label d}
include D B hk h
set_option maxHeartbeats 200000 in
lemma signLeaf {t:C.label e}{a:Finset I} (s: Viewers U) (hp:SignDir C S k b m l d e o A' o' A x v a φ y t)
    (hs:Screen Z!) (hx:Injective (beside (Z!) Y)) (hy:Injective (beside (Ξ!) Y)) (hY:ClearOf 0 Y c): ‖card_read (C:=C) (spectator U s) (chunk a Z!) (chunk a v) Y w - unit_read (C:=C) (spectator U s) t Y w‖ ≤ A*α:=by
    obtain ⟨g,p,V,f,f',hb,hh,hf,hE,hF,hT⟩:=hp.ready; let X:= chunk a x; have ht: Injective (beside (chunk a Z!) Y):= affiliate hx; have hΞ: chunk a Z! = C.S.gridPoint k ∘ X:=rfl
    rw [hΞ,← card_same (x:=X) (Y:=Y) U (chunk a p) (show S.classTokens ∘ _= S.classTokens ∘ chunk a v from funext fun i=> congr_fun hf.ongoing i.val) ht s]; exact first_read (x:=X) (f:=g) (Y:=Y) (v:=chunk a p) (k:=k) (z:=f') U B D hk s (le_trans hh h) (V:=fun i=>V i.val) (hT.mono fun i h=> h.1) (pinned hs) (fun i=>hf.values i.val) hF.wins ht hy hY
end Probe
end YM.OPE.Log.Trunk.Shuttle
