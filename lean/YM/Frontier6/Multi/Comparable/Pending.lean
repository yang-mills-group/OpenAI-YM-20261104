import YM.Frontier6.Multi.Comparable.Rolling
import YM.Frontier6.Multi.Comparable.Credit

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
lemma Aspect.alive {u:I→ O→ E4} (h:Aspect T u): ∀ᶠ i in T.via,Injective (u i):=by
    filter_upwards [eventually_all.mpr fun i:O=>eventually_all.mpr fun j:O=> eventually_all.mpr fun k:i≠j=>(h.2 k).pos] with i hi s t hp
    by_contra ht; have hC:= hi s t ht; rw [hp,sub_self,norm_zero] at hC; exact lt_irrefl _ hC
lemma Aspect.visible (d:ℕ) (c:I→ E4) (t:O→S.Tag) {x:I→O→ E4}(h:Aspect T x): ∀ᶠ i in T.via,Visible K (c i) d (assembly S (fun k=> x i k+c i) t):=by
    obtain ⟨s,hs,hP⟩:= Frontier6.Safe.limits K d
    filter_upwards [eventually_all.mpr fun k:O=> (h.1 k).from_allowance (T.minted_c _ hs) (by norm_num), h.alive] with i hi hk
    exact visibles K _ hP (fun _ _ he=> hk (add_right_cancel he)) (fun j=>by simpa only [add_sub_cancel_right] using hi j) t
include h h' hG hh hc hξ hx hm he hq ht hA hw root
lemma tribunal (d:ℕ) (hk:Bench C.S T k b) (hp:0<b)(hz:b<a):
    ∃ v:I→ S.Field d,
    (∀ b:Fin (d+1), T.Costs (fun i=> weight K b (reach K d b (v i))) (ψ-(b.val:ℝ)*a)) ∧
    Permit K T ξ j k (fun i x=> X i x -letter S x ⟨d,v i⟩) (-(welcome t d a c b ε)) ∧
    T.Costs (fun i=> absorb K 0 d (X i 0)-v i) (-(welcome t d a c b ε)):=by
    obtain ⟨v,hv,hP⟩:= credit K hξ hc d h h' hG hx hm hk t p z root he hq hp hz hw ht hA
    refine ⟨v,hv,hP,(pricing K hP 0 d hk hp hξ hc hh).cf ?_⟩; filter_upwards [ht.visible K d 0 (fun k:O=> S.classTokens (⟨t k,p k⟩:C.book.Token))] with i hi; simp only [Pi.zero_apply,Function.comp_apply] at hi ⊢; rw [absorb_sub K hi (apo_letter K _ _ _), absorb_letter]

lemma nearEnough (d:ℕ)(ha:0<a): ∀ b:Fin (d+1), T.Costs (fun i=> weight K b (reach K d b (absorb K 0 d (X i 0)))) (ψ-(b.val:ℝ)*a):=by
   let q:= a/(32*(d+1:ℕ)); have h0 : 0<q:=by unfold q; positivity
   have h1 : q<a:= by unfold q; apply div_lt_self ha _; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) d]
   obtain ⟨p',hk'⟩:= picks C.S C.path.levels.fits.mesh T q h0
   obtain ⟨u,hU,hV,hP⟩:= tribunal K h h' hG hh hc hξ hx hm t p z root he hq hw ht hA d hk' h0 h1
   intro i
   let F:= weight K i ∘L reach K d i; let v b:= absorb K 0 d (X b 0)
   have hd:d*q ≤ a/32:=by
      suffices (d+1:ℕ)*q=a/32 from (le_trans ?_ this.le); swap; · unfold q; field_simp
      apply mul_le_mul_of_nonneg_right ?_ h0.le; exact_mod_cast Nat.le_succ d
   have hH: -(welcome t d a c q ε) ≤ ψ-i*a:=by
       unfold welcome; have hq:q ≤ a/32:=by unfold q; apply div_le_div_of_nonneg_left ha.le (by norm_num); push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) d]
       have hi:(i:ℝ) ≤ d:= by exact_mod_cast (show (i:ℕ) ≤ d by omega)
       nlinarith only [hd,hq,ha,mul_le_mul_of_nonneg_right hi ha.le] -- q ≤ a/2
   refine (((hP.mapped F).too hH).add (hU i)).cf (Eventually.of_forall (fun z=>?_)); change F (_- _) + F (u z)=F (v z); rw [map_sub,sub_add_cancel]
end YM.Frontier6.Road
