import YM.Frontier6.Multi.Comparable.Pending

/-! Running from stamped data to arbitrary deep releases. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word Fareway Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S:Table C.book}
variable (K:Final C H S){ξ:Ultrafilter (ℕ×ℕ)}{T:Fareway I}{j m k:I→ℕ}{a b c ε:ℝ}
open PhysicalNext.Repeat.Legato Canvas Next.Extract Dash
variable {O:Type}[Fintype O][DecidableEq O]
variable {T':Table C.book}{L:ℕ→Table C.book}{R:Bin T'}{Y:DiffPlan S}
variable (h:Base C H T' L R S Y) (h':Realm C)(hG:G.Simple) (hh:Org.Grill C H) (hc:Extraction.Wcmain C) (hξ:ξ.toFilter≤H.fuse)
    (hx:Bench C.S T j c)(hm:Bench C.S T m a)(hk:Bench C.S T k b)
    (t:O→ℕ)(p:(i:O)→ C.label (t i))(z:I→O→ Cover) (root:O)
set_option quotPrecheck false
local notation "A"=>fun i:I=> C.S.gridPoint (j i) ∘ z i
local notation "X"=>fun (i:I)(x:E4)=> assembly S (fun u=>C.S.gridPoint (j i) (z i u)+x) (fun k:O=> S.classTokens (⟨t k,p k⟩:C.book.Token))
local notation "ψ"=>forestPower t a c ε
variable (he:a<1)(hq:1<c)(hp:0<b)(hz:b<a)(hw:0<ε)(ht:Aspect T (fun i=> C.S.gridPoint (j i) ∘ z i))(hA:∀ᶠ i in T.via,∀ a:Axis,Injective (fun b=> (C.S.gridPoint (j i) (z i b)) a))
lemma apparels (d:ℕ)(V0:I→ S.Field d)(y:ℝ)(h:∀ i: Fin (d+1), Permit K T ξ j k (fun n x=>letter S x ⟨i.val, weight K i (reach K d i (V0 n))⟩) y) (hξ:ξ.toFilter ≤ H.fuse) : Permit K T ξ j k (fun n x=> letter S x ⟨d,V0 n⟩) y:=by
    let Y(i:Fin (d+1))(n:I)(x:E4):= suit K x i (reach K d i (V0 n)); have ht(i): Permit K T ξ j k (Y i) y:= (h i).same (Eventually.of_forall fun _ _=> (suit_reads K _ _ _).symm K)
    refine (Permit.sums hξ Y Finset.univ (fun i _=> ht i)).same (Eventually.of_forall fun n x=>?_); change Tale.Congr _ (∑ i:Fin (d+1),suit K _ _ _) _; rw [← deck_eq]; exact deck_at K x d _ -- Congr def unfolding

local notation "θ"=>fun d:ℕ=>fun i:I=>absorb K 0 d (X i 0)
local notation "Z"=> fun d:ℕ=>ψ + b - (d:ℝ)*(a-b)^2
include h h' hG hh hc hξ hx hm he hq ht hA hw root hk hp hz
lemma gram (d:ℕ): Permit K T ξ j k (fun i x=>letter S x ⟨d, θ d i⟩) (ψ+b):=by
    have hh:= nearEnough K h h' hG hh hc hξ hx hm t p z root he hq hw ht hA d (hp.trans hz)
    refine apparels K d _ _ (fun i=>?_ ) hξ
    apply (ticket_focus K hξ hc _ hk zero_lt_one _ (hh i)).exceeds; linarith only [mul_le_mul_of_nonneg_left hz.le (Nat.cast_nonneg (α:=ℝ) i.val)]
-- some inequalities with i.val.
lemma citation (d:ℕ) : Permit K T ξ j k (fun i x=> X i x - letter S x ⟨d,θ d i⟩) (Z d):=by
   obtain ⟨u,hU,hP,hT⟩:= tribunal K h h' hG hh hc hξ hx hm t p z root he hq hw ht hA d hk hp hz
   let F i:= θ d i; have hh':= nearEnough K h h' hG hh hc hξ hx hm t p z root he hq hw ht hA d (hp.trans hz)
   let E(d:ℕ):= Z d; let k':= d; have hv : a-b ≤ 1:=by linarith
   have hx0:0 ≤ a-b:=by linarith
   let v i:= F i-u i
   have hD : Permit K T ξ j k (fun i x=> letter S x ⟨d,v i⟩) (E d):=by
      apply apparels (K:=K) d -- arguments
      · intro i; let Q:=weight K i ∘L reach K d i; let x:ℝ:= (i:ℕ); let y:= Q ∘ v
        change Permit K T ξ j k (fun i' x=> letter S x ⟨(i:ℕ),y i'⟩) _
        rcases le_total (d*(a-b)) x with hi|hi
        · have he' : T.Costs y (ψ-x*a):= ((hh' i).sub (hU i)).cf (Eventually.of_forall fun i=>by change Q (F _) - Q _ = Q (_-_); rw [map_sub])
          apply (ticket_focus K hξ hc _ hk zero_lt_one y he').exceeds; change (x+1)*b+ _ ≤ _; unfold E; linarith only [mul_le_mul_of_nonneg_right hi hx0]
        have hp': T.Costs y _:= hT.mapped Q
        apply (ticket_focus K hξ hc _ hk zero_lt_one y hp').exceeds; change (x+1)*b+ -(welcome ..) ≤ _; unfold E welcome; push_cast; nlinarith only [hx0,mul_le_mul_of_nonneg_right hi hp.le, mul_le_mul_of_nonneg_right (show a≤1 from he.le) (mul_nonneg (Nat.cast_nonneg d) hx0)]
      exact hξ
   have hE: -(welcome t d a c b ε) ≤ E d:=by unfold E welcome; nlinarith only [pow_le_pow_of_le_one hx0 hv (show 1 ≤ 2 by omega),hx0,hp, mul_nonneg (Nat.cast_nonneg d) (show 0 ≤ a-b-(a-b)^2 from sub_nonneg.mpr (by simpa using pow_le_pow_of_le_one hx0 hv (show 1 ≤2 by omega)))]
   refine ((hP.exceeds hE).minus hD).same (Eventually.of_forall fun i x Y s=>?_)
   change poll S (state K s) ((X i x-letter S x ⟨d,u i⟩-letter S x ⟨d,F i-u i⟩)*Y)=_ ; simp_rw [sub_mul,map_sub,← reads K,map_sub]; -- RHS function application reduces?
   abel

lemma liftoff (d:ℕ): Permit K T ξ j k X (ψ+b):=by
    have hL:= gram K h h' hG hh hc hξ hx hm hk t p z root he hq hp hz hw ht hA d
    let Y i x:= letter S x ⟨d,θ d i⟩
    have ht':= citation K h h' hG hh hc hξ hx hm hk t p z root he hq hp hz hw ht hA d
    have hy: Z d ≤ ψ + b:= sub_le_self _ (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _)); exact ((ht'.exceeds hy).merge hL).same (Eventually.of_forall fun i x=> by rw [sub_add_cancel]; exact almost K _)
end YM.Frontier6.Road
