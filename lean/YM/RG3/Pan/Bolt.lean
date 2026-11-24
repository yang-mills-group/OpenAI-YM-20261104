import YM.RG3.Pan.Bath

/-!
# Arbitrary route in true curvature palette

A path interpreted as based group product of small faces, in the same
orientation convention as the Spindle. Input radius scales as c/length after
this operation. Polynomial bill at every fixed order, with constants explicit
in Bath and horizon k. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan
open Lattice Wilson Function WilsonStartup
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
 [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k : ℕ}

lemma Bill.plain {x : E} (L : E→L[ℝ] F) {A d : ℝ} {f : F→Y}
    (h : Bill k A d f (L x)) (hL : ∀ v, ‖L v‖ ≤ ‖v‖) : Bill k A d (f ∘ L) x:= by
  refine ⟨h.smooth.comp _ L.contDiff.contDiffAt,fun i hi=>?_⟩
  rw [WardBin.Lies.liner L (h.smooth.of_le (Nat.cast_le.mpr hi))]
  have hs := (norm_nonneg _).trans (h.B i hi)
  apply FreeResolvent.Affine.slot_op hs
  intro l hl; rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine (ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (fun j=>(hL (l j)).trans (hl j))).trans ?_
  simpa using h.B i hi

/-- The estimate before reading logs on representative paths, not
requiring a coherent fake off-field palette. True faces are separately
plugged in. -/
abbrev MapSet (ι : Type*) (G : Gauge) := ι→G.Color

variable {ι : Type*} {G : Gauge}

def flourish {K : Type*} [Group K] (v:ι→K) (i : ι × Bool) := if i.2 then (v i.1)⁻¹ else v i.1

def stream (v : MapSet ι G) (p : List (ι × Bool)) := (p.map (flourish (recover G ∘ v))).prod

@[simp] lemma stream_nil (v : MapSet ι G) : stream v []=1:=rfl
@[simp] lemma stream_cons (v : MapSet ι G) (a p) : stream v (a::p) = flourish (recover G∘v) a*stream v p:=rfl
@[simp] lemma stream_blank (G : Gauge) (p : List (ι × Bool)) : stream (0: MapSet ι G) p = 1:= by
  induction p with
  | nil=> rfl
  | cons a p ih=> rw [stream_cons,ih,mul_one]; unfold flourish; split <;> simp

/-- Normalize lemma to reuse chorus at arbitrary domain. -/
lemma recital (v : MapSet ι G) (p : List (ι × Bool)) :
    stream v p=bands (fun (i:ι × Bool) (v : MapSet ι G)=>flourish (recover G ∘ v) i) p v := rfl

/-- Exact for true chords in range. -/
lemma enacted (Q : Bath G k) (u : ι→G.El) (p : List (ι × Bool))
    (h : ∀ i∈p,G.chord (u i.1) ≤ Q.tile) :
    stream (G.curvature ∘ u) p=(p.map (flourish u)).prod := by
  induction p with
  | nil => rfl
  | cons a p ih=>
    rw [stream_cons,List.map_cons,List.prod_cons,ih (fun i hi=>h _ (List.mem_cons_of_mem _ hi))]
    simp only [flourish,Function.comp_apply,Q.north _ (h _ List.mem_cons_self)]

variable [Fintype ι]

def span (Q : Bath G k) (n : ℕ) := 1+2^k*Q.price*(n:ℝ)
lemma span_one_le (Q : Bath G k) (n : ℕ) : 1 ≤ span Q n := le_add_of_nonneg_right (by have he:=Q.extra; positivity)
lemma span_le (Q : Bath G k) : Monotone (span Q) := by
  intro x y hi; unfold span; have hp := Q.extra; gcongr

lemma lights (Q : Bath G k) (v : MapSet ι G) (hv : ‖v‖ ≤ Q.tile) (N : ℕ) (p : List (ι × Bool)) (hw : p.length ≤ N):
    Bill k ‖(1:G.Mat)‖ (span Q N) (fun z=> G.mat (stream z p)) v:= by
  let u (i:ι × Bool) (v : MapSet ι G):G.El:=flourish (recover G ∘ v) i
  have hl (i:ι×Bool) : GroupHit k Q.price 1 (u i) v := by
    have h0 : GroupHit k Q.price 1 (fun z : MapSet ι G=> recover G (z i.1)) v := by
      let L:MapSet ι G→L[ℝ] G.Color:= ContinuousLinearMap.proj i.1
      exact Bill.cast ((Q.spin (L v) ((norm_le_pi_norm v i.1).trans hv)).plain L (fun x=> norm_le_pi_norm x i.1))
    unfold u flourish; split
    · exact h0.backtrack (zero_le_one.trans Q.extra) zero_le_one
    exact h0
  simp_rw [recital]
  have ht:= song_bill (u:=u) p (zero_le_one.trans Q.extra) zero_le_one (fun i _=>hl i)
  rw [mul_one] at ht
  exact ht.drift (zero_le_one.trans (span_one_le ..)) (span_le _ hw) (norm_nonneg _)

lemma voyage (Q : Bath G k) (v : MapSet ι G) (hv : ‖v‖ ≤ Q.tile) (N : ℕ) (p : List (ι × Bool)) (hw : p.length ≤ N):
    G.chord (stream v p) ≤ N* (Q.price * ‖v‖):= by
  refine le_trans (b:=p.length*(Q.price*‖v‖)) ?_ (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hw) (mul_nonneg (zero_le_one.trans Q.extra) (norm_nonneg _)))
  clear hw
  induction p with
  | nil=> simp
  | cons a p ih=>
    rw [stream_cons,List.length_cons,Nat.cast_add_one,add_mul,one_mul, add_comm (_*(_*_)) (Q.price*‖v‖)]
    refine (G.chord_triangle ..).trans (add_le_add ?_ ih)
    unfold flourish; split
    · rw [G.chord_inv]
      exact (Q.bill _ ((norm_le_pi_norm v a.1).trans hv)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v a.1) (zero_le_one.trans Q.extra))
    exact (Q.bill _ ((norm_le_pi_norm v a.1).trans hv)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v a.1) (zero_le_one.trans Q.extra))

def record (p : List (ι × Bool)) (v : MapSet ι G) := G.plog (G.mat (stream v p))
def bolt (Q : Bath G k) := cap k ‖(1:G.Mat)‖ Q.price 1
lemma bolt_pos (Q : Bath G k):1≤bolt Q:=Q.extra.trans (cap_ge k (norm_nonneg _) (zero_le_one.trans Q.extra) zero_le_one)

/-- Take a real analytic path LOG only on the indicated smaller palette
ball; exact represented price and inverse. -/
lemma posed {τ:ℝ} (Q : Bath G k) (v : MapSet ι G) (hτ : τ ≤ Q.tile) (h : ‖v‖ ≤ τ) (N : ℕ) (p : List (ι × Bool)) (hw : p.length ≤ N) (hed : N* (Q.price * τ) ≤ Q.tile):
    Bill k (bolt Q) (span Q N) (record p) v ∧
      ‖record p v‖ ≤ Q.price^2*N*τ ∧ G.lieExp (record p v)=stream v p:= by
  have hn:=Q.extra; have hc:=zero_le_one.trans hn; have hN:=Nat.cast_nonneg (α:=ℝ) N
  have hV:=h.trans hτ
  have hy:= (voyage Q v hV N p hw).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hc) hN)
  have ht:=hy.trans hed
  refine ⟨(lights Q v hV N p hw).comp (g:=G.plog) (Q.turn _ ht) zero_le_one (zero_le_one.trans (span_one_le ..)),?_,Q.true _ ht⟩
  exact (Q.shear _ ht).trans ((mul_le_mul_of_nonneg_left hy hc).trans_eq (by ring))
end YM.RG3.Pan
