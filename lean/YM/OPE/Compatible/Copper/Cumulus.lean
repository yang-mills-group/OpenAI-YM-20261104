import YM.OPE.Compatible.Signals.Credited
import YM.OPE.Compatible.Pendulum.Deposit
/-!
# Variant of `mirrorMatch` for two variable readouts and three registers on root signed balance.

Screen needs only within each. Supports within some other difference needn't be disjoint. This file is downstream using `Org.Grill` eventually, unrelated to any perturbative sector inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word
open Cards Bid Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book} (U: Final C F S)
variable {I J Z : Type}[Fintype I][Fintype J][Fintype Z] {N p k f b l n q: ℕ}
   {d:ℕ}{t:ℝ} -- del
variable {x:I→ Cover}{z:Z→ Cover}{v:I→ C.book.Token}{u:Z→ C.book.Token}{w:J→ C.book.Token}{y:J→ Cover}
   {φ:Filter (ℕ×ℕ)}[φ.NeBot]{B:J→ℝ}
   {D: ReadLabel C v}{L: ReadLabel C u}{Q:C.label d}{g:ℕ×ℕ→ C.label d}
set_option quotPrecheck false
local notation "T"=> C.S.gridPoint k
local notation "X!"=>fun _ :Unit=> (0:Cover)
local notation "A"=> register C k
local notation "Φ"=> fun _ : Unit=> (⟨d,Q⟩:C.book.Token)
omit [φ.NeBot] in
lemma TileDoc.triad {L':ReadLabel C w}(hx:Screen (T ∘  x))(hz:Screen (T ∘ z))(hy:Screen (T ∘  y)) (hp:∀ i,Tendsto (D i) φ (𝓝 (v i).2))(hq:∀ i,Tendsto (L i) φ (𝓝 (u i).2))(hQ:∀ i,Tendsto (L' i) φ (𝓝 (w i).2)): TileDoc U k φ ((viewing U (T ∘  x) v-viewing U (T ∘  z) u)-viewing U (T ∘  y) w) ((register C k x (germ D)-register C k z (germ L))-register C k y (germ L')):=by
    let a:Spark C φ k := {Index:=I,x:=x,v:=v,q:=D,limit:=hp,frames:=hx}; let r:Spark C φ k := {Index:=Z,x:=z,v:=u,q:=L,limit:=hq,frames:=hz}; let b':Spark C φ k:= {Index:=J,x:=y,v:=w,q:=L',limit:=hQ,frames:=hy}; have he:=TileDoc.sparks U 3 ![1,-1,-1] ![a,r,b']; simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,neg_smul,one_smul,neg_mul,one_mul, ← sub_eq_add_neg] at he; exact he
variable (h : Org.Grill C F)
include h
lemma mirrorThird (hk:b ≤ k)(hp:Gap C.S k y (2*C.S.a l))(hd:GapTo C.S k (X!) y (2*C.S.a b))
    (hf:Screen (beside ((T)  ∘  x) ((T)  ∘  y)))(hf':Screen (beside (T ∘  z) (T ∘  y)))
    (hx:Screen (beside ((T)  ∘  X!) ((T)  ∘  y)))
    (he:Hall C.S b l q f n 1 (Fintype.card J)) (hr:φ≤ F.fuse) (hU:∀ i,Tendsto (D i) φ (𝓝 (v i).2))(ht:∀ i,Tendsto (L i) φ (𝓝 (u i).2))(hz:Tendsto g φ (𝓝 Q))
    (hB : ∀ᶠ i:ℕ×ℕ in φ, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) t ((register C k x (germ D) i.1 i.2-register C k z (germ L) i.1 i.2)-C.O i.1 i.2 (g i) 0))
    (hD: Prepared (C:=C) w F n B) :
    ‖(viewing U (beside (T  ∘  x) (T  ∘  y)) (beside v w)-viewing U (beside (T  ∘  z) (T ∘ y)) (beside u w))- viewing U (beside (T  ∘  X!) (T  ∘  y)) (beside (sole (⟨d,Q⟩: C.book.Token)) w)‖ ≤ t * ∏ i,B i:=by
    rw [← beside_commutes] at hf hf' hx; rw [← beside_commutes,← beside_commutes,← beside_commutes]
    let Y:=frozen C w; let V := sole (⟨d,Q⟩: C.book.Token); let R:ReadLabel C V:=fun _=>g; let W:Cylinder C:=fun N p=> C.O N p (g (N,p)) 0; let H:Cylinder C:=fun N p=> A x (germ D) N p- A z (germ L) N p-W N p
    have hu {I : Type}(v:I→ C.book.Token)(Z:ReadLabel C v)(hp : ∀ i,Tendsto (Z i) φ (𝓝 (v i).2)): ∀ i,Tendsto (combine Z Y i) φ (𝓝 ((beside v w i).2)) :=by intro i;cases i; exact hp _; exact tendsto_const_nhds
    have hy:= TileDoc.triad U hf hf' hx (hu _ _ hU) (hu _ _ ht) (hu _ R (fun _=>hz)); have hl: Gap C.S k X! (2*C.S.a b) :=fun a b h=> (h (Subsingleton.elim ..)).elim
    apply le_trans (TileDoc.global U hy (B:=sole t) h hk hr hl hp hd he (z:=fun _=>H) (w:=germ Y) (fun _=>hB) (fun j=>(hD.here j).filter_mono hr) ?_) (by simp [sole])
    filter_upwards with i; simp only [Pi.sub_apply]; rw [works,works,works,just_one H, show germ R=(fun _=>W) from rfl, just_one W]; unfold H; rw [sub_mul,sub_mul]
end YM.OPE
