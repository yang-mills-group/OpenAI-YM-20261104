import YM.Frontier6.Multi.Comparable.Solo
import YM.Frontier6.Multi.Tale.Product
/-! Detector costing on any admitted surfaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word Fareway
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S:Table C.book}
variable (K:Final C H S){ξ:Ultrafilter (ℕ×ℕ)}{T:Fareway I}{j k:I→ℕ}{a b:ℝ}

lemma Wide.uniform {x:I→V→ E4} {T:Fareway I} (r:ℝ)(hr:0 < r)(he:∀ᶠ i in T.via, Pairwise fun j k=> r < ‖x i j-x i k‖) : Wide T x 0:=by
   intro j k hj b hb; filter_upwards [he, (T.minted (-b)).cheaper (T.minted_c r hr) (by linarith)] with i hi he using he.le.trans (hi hj|>.le)

lemma Fareway.Costs.uniform {J:Type*}{X:Type*}[SeminormedAddCommGroup X] {T:Fareway I} {v : I→ J→ X}(h:∀ p:I→J, T.Costs (fun i=>v i (p i)) a) (he:a<b):∀ᶠ i in T.via,∀ j,‖v i j‖ ≤ Real.exp (T.scale i*b):=by
   cases isEmpty_or_nonempty J with
   | inl he=> exact Eventually.of_forall fun _=>isEmptyElim
   | inr hy=>
     by_contra hw; let f(i:I):J:= if h:∃ j,Real.exp (T.scale i*b) < ‖v i j‖ then h.choose else Classical.choice hy
     apply hw; filter_upwards [h f b he] with i hi j; by_contra ht
     have hp:∃ j,Real.exp (T.scale i*b) < ‖v i j‖:= ⟨j, lt_of_not_ge ht⟩
     have he := hp.choose_spec; unfold f at hi; rw [dif_pos hp] at hi; exact not_lt.mpr hi he

section
variable [Fintype V][DecidableEq V]
variable {X:BasisRay S I}(h:Permit K T ξ j k X a)
include h
-- unselected OR every character, varying label stage. just a finite widened permit call (no state charging from α spectr.)
lemma salary (hk:Bench C.S T k b)(hb:0<b)(hξ:ξ.toFilter≤H.fuse)(hW:Extraction.Wcmain C)(hG:Org.Grill C H)
   (c:I→ E4) (p:V→I→ E4)(d:V→ℕ) (v:∀ i:V,I→ S.Field (d i))
   (hy:Wide T (fun i (t:Option V)=> t.elim (c i) (fun j:V=>p j i)) 0) (hw:∀ i,T.Costs (v i) 0) (s:I→ StateIndex K): T.Costs (fun i=> poll S (state K (s i)) (X i (c i)*∏ j:V,letter S (p j i) ⟨d j,v j i⟩)) a:=by
   intro z hz; let M:=∑ i:V, ((d i:ℝ)+1); have hm:0 ≤ M:= Finset.sum_nonneg (fun _ _=>by positivity)
   let x:= min b ((z-a)/(2*(M+1))); have hx:0 < x:= lt_min hb (div_pos (sub_pos.mpr hz) (by positivity))
   let γ:ℝ:= M*x; have hz':a+γ < z:=by
      have hr:(M+1)*x ≤ (z-a)/2:=by have hl : x≤ (z-a)/(2*(M+1)):= min_le_right ..; have he := (le_div_iff₀ (by positivity : (0:ℝ)<2*(M+1))).1 hl; linarith only [he]
      unfold γ; linarith only [hr,hx,hz]
   obtain ⟨m,hm0⟩:= picks C.S C.path.levels.fits.mesh T x hx; obtain ⟨l,hp'⟩:= picks C.S C.path.levels.fits.mesh T (x/2) (half_pos hx)
   let y(i)(t:Option V):= t.elim (c i) (fun j:V=>p j i); let X' (i:Option V): BasisRay S I:= i.elim X (fun j t z=> letter S z ⟨d j,v j t⟩); let a' (i:Option V) : ℝ:= i.elim a (fun j:V=> ((d j:ℝ)+1)*x); let r (i:Option V):I→ℕ:= i.elim k (fun _=>m); let b' (i:Option V):ℝ:= i.elim b (fun _=> x)
   have hP : ∀ i:Option V, Permit K T ξ j (r i) (X' i) (a' i):=by
      intro i; cases i; exact h; next i=> exact by simpa only [add_zero] using! ticket_focus (j:=j) K hξ hW (d i) hm0 zero_lt_one _ (hw i)
   have ht : T.Costs (fun i=> poll S (state K (s i)) (∏ v:Option V, X' v i (y i v))) (∑ v:Option V,a' v):= budget_product y r hξ X' a' hP hp' (fun i=>by cases i; exact hk; exact hm0 : ∀ i : Option V,Bench C.S T (r i) (b' i)) ?_ (half_pos hx) zero_lt_one hy s hG
   swap; · intro i; cases i; exact (half_lt_self hx).trans_le (min_le_left ..); exact half_lt_self hx
   simp_rw [Fintype.sum_option, Fintype.prod_option] at ht
   exact ht z (show a + ∑ i,((d i:ℝ)+1)*x < z from by rw [← sum_mul]; exact hz')
end
end YM.Frontier6.Road
