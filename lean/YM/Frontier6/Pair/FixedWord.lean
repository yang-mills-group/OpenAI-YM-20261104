import YM.Frontier6.Pair.Marginal

/-! Tools for pricing raw or projected single columns sent to the spectator cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Set Filter Function MeasureTheory Lattice Cells Wilson Extraction Spec Bid Work.B15 Next.UVStress OS MergeProof.Ribbons Around Word
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{b k l N p n : ℕ} (v:Fin n → C.book.Token)

/-- Spectator service at stop `b`; require positive margin for gauge-root `y`.
Give the single-slot one-tower cost (power can be made sharper later). -/
lemma services_one (y:C.book.Token) (h:CellHyp C F)(hC:C.Makes) : ∀ᶠ k:ℕ in atTop, ∀ (b l:ℕ)(x:Cover)(u:Cover), b ≤ k → b ≤ l → atStop C.S b u (3*C.S.a k) (C.S.gridPoint l x) →
   ∀ᶠ i:ℕ×ℕ in F.fuse, ∃ (hN:b≤ i.1)(g: Config G (C.side i.1 i.2)→ℂ),
      let T:=center C.S i.2 hN 0
      Interior (T.chamber 0) g ∧ T.rootTest (C.beta i.1 i.2) g ≤ Real.exp (((y.1:ℝ)+2)*C.S.scale k) ∧
        C.O i.1 i.2 y.2 (location C.S l i.1 i.2 x)=T.copy (wrap T.period u) g := by
   filter_upwards [spectra (v:=fun _:Fin 1=>y) h] with k hk b l x u hb hl hx
   filter_upwards [large_mesh F l,hk] with i hr he
   obtain ⟨N,p⟩:=i; obtain ⟨hp,hV⟩:=he
   let T:=center C.S p (hb.trans hp) 0; let Y:T.Cell:= wrap T.period u
   let v:=location C.S l N p x; let A:= Real.exp (((y.1:ℝ)+2)*C.S.scale k)
   obtain ⟨g,hg,hZ,hU⟩:=Lease.alive (q:=fun _:Fin 1=>y) (T:=T) hC 0 v (A:=A) (k:=k) ⟨hp,hV⟩ hp (inherits (C:=C) hb hp) (z:=Y) (at_margin C.S p u x hl hr hp hx)
   exact ⟨hb.trans hp,g,hZ,hU,hg.symm⟩

def stillStory (F:Extraction.Order)(m k : ℕ)(factor:Fin m→ℂ)(images:Fin m→ℕ)(Y:Π i:Fin m, Fin (images i)→ Cover)(v:Π i:Fin m, Fin (images i)→ C.book.Token)(hg:∀ i,Extraction.Order.grid C k (Y i)∈generic (images i)) : Episode C F k where
   num:=m
   factor:=factor
   image:=images
   seats:=Y
   gen:=hg
   weight i j:=(v i j).1
   point i j:=(v i j).2
   current i j _ _:=(v i j).2
   views i j:=⟨Eventually.of_forall fun _=>trivial,fun _ => (v i j).2,fun _ _=> tendsto_const_nhds, tendsto_const_nhds⟩

def story (F:Extraction.Order)(w:Fin n → Cover)(hg:Extraction.Order.grid C l w∈generic n): Episode C F l:= stillStory F 1 l 1 (fun _=>n) (fun _=>w) (fun _=>v) (fun _=>hg)
lemma story_eq (F:Extraction.Order)(w:Fin n → Cover)(hg:Extraction.Order.grid C l w∈generic n) (S:Table C.book) : fieldWord (story v F w hg) S=S.read (Extraction.Order.grid C l w) v:=by
    -- Episode constant label reconstructs
    change (∑ _ : Fin 1, (1:ℂ)* S.expect (realize v (Extraction.Order.grid C l w)))= _; simp
lemma story_cuts (F:Extraction.Order)(w:Fin n → Cover)(hg:Extraction.Order.grid C l w∈generic n)(N p:ℕ)(U:Config G (C.side N p)): (story v F w hg).cuts N p 0 U=∏ i:Fin n,C.O N p (v i).2 (location C.S l N p (w i)) U:=by
   change (∑ _ : Fin 1, (1:ℂ)* ∏ i:Fin n, C.O N p (v i).2 (location C.S l N p (w i+0)) U)=_; simp

variable {S:Table C.book}(K:Spec.Final C F S)
def headline (C:Family G)(k:ℕ)(v:C.book.Token):= Real.exp (((v.1:ℝ)+2)*C.S.scale k)
open Org in
lemma story_period (h:Grill C F) : ∀ᶠ k:ℕ in atTop, ∀ b l (x u:Fin n → Cover), b ≤ k → b ≤ l → Injective u → Extraction.Order.grid C l x ∈ generic n → (∀ i, atStop C.S b (u i) (3*C.S.a k) (C.S.gridPoint l (x i))) → ∀ i:StateIndex K,
    ‖(state K i).read (Extraction.Order.grid C l x) v‖ ≤ ∏ i,headline C k (v i):=by
   filter_upwards [eventually_all.mpr fun i=> services_one (v i) K.room.copies K.room.cutoff] with k hk b l x u hb hl hi hx hX s
   rw [← story_eq v F x hx]; refine lectern K _ u hi s h hl (le_refl _) (fun i=>_) (fun i=>Real.exp_pos _|>.le) ?_
   filter_upwards [large_mesh F b,eventually_all.mpr fun i=> hk i b l (x i) (u i) hb hl (hX i)] with i hN he
   obtain ⟨N,p⟩:= i
   choose _ g hg using he;refine ⟨hN,g,fun i=>⟨(hg i).1,(hg i).2.1⟩,funext fun U=>?_⟩
   rw [story_cuts]; exact Finset.prod_congr rfl fun i _=> congr_fun (hg i).2.2 U
end YM.Frontier6.Platform
