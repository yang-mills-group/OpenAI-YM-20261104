import YM.WilsonCoeffUV.Vacuum.UV.LogAge
/-!
# Per-filter seats (`poly`) made from exact calendars Ω
Clock spreads in ℝ, coefficients in ℂ. We'll use intrinsic finite tables +
polynomial charge.Stored poly estimates mean all prices through fixed order, never uniform in that order.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission
open WilsonCoeffUV.Bank Function Filter Set
open scoped BigOperators Topology ContDiff Classical
variable {ι ι' σ σ':Type*}
variable (l:Filter ι)(q:ι→ℝ)
abbrev Maxer (l:Filter ι)(Y:ι→ℝ): Prop:= ∀ᶠ i in l,1≤ Y i
abbrev BoundPoly (f:ι→ℝ) : Prop:= ∃ T:Credit,∀ᶠ i in l, f i≤ T.buy (q i)
abbrev Billed {E:Type*}[Norm E](f:ι→ E) : Prop:= BoundPoly l q (norm ∘ f)
namespace BoundPoly
variable {l q} (h:Maxer l q) {x y:ι→ℝ}
lemma pureP (p:ℝ): BoundPoly l q (fun _=> p):=⟨ {d:=0,x:=max p 1, good:=le_max_right ..}, Eventually.of_forall fun i=>by simp only [Credit.buy,pow_zero,mul_one,le_sup_left]⟩
lemma grow (X:BoundPoly l q x)(Y:y≤ᶠ[l] x):BoundPoly l q y:=⟨X.choose,Y.trans X.choose_spec⟩
lemma transport (X:BoundPoly l q x)(a0:Filter ι')(f:ι'→ι)(v:Tendsto f a0 l): BoundPoly a0 (q∘f) (x∘f):=⟨X.choose, v.eventually X.choose_spec⟩ -- universe
lemma Maxer.book : BoundPoly l q q:= ⟨Credit.leanC, Eventually.of_forall (fun i=> by simp only [Credit.lean_cost,le_rfl])⟩
include h
lemma plusP (X:BoundPoly l q x)(Y:BoundPoly l q y): BoundPoly l q (x+y):=by obtain ⟨U,hU⟩:= X; obtain ⟨V,hV⟩:=Y; refine ⟨U.plus V,?_⟩; filter_upwards [h,hU,hV] with i p v y; exact (add_le_add v y).trans (Credit.fuel _ _ p)
lemma plusF (X:BoundPoly l q x)(Y:BoundPoly l q y): BoundPoly l q (fun i=>x i+y i):= plusP h X Y
lemma mulP (X:BoundPoly l q x)(Y:BoundPoly l q y)(u:∀ᶠ i in l,0≤ y i): BoundPoly l q (x*y):=by
   obtain ⟨U,hU⟩:= X; obtain ⟨V,hV⟩:= Y; refine ⟨U.prodC V,?_⟩; filter_upwards [h,hU,hV,u] with i p v y z; exact (mul_le_mul v y z (zero_le_one.trans (U.purchase p))).trans_eq (Credit.products ..).symm
end BoundPoly
namespace Billed
variable {R E F:Type*}{l q} (h: Maxer l q)
lemma comp {X:Type*}[Norm E] (u:Filter X)(f: X→ι)(v:Tendsto f u l)(y:ι→ E)(p:Billed l q y): Billed u (q ∘ f) (y ∘ f):= BoundPoly.transport p u f v
section mono
variable [NormedAddCommGroup E] [NormedAddCommGroup F] {x y:ι→E}
lemma room {B:ι→ℝ}(u:BoundPoly l q B)(v:norm ∘ x≤ᶠ[l] B): Billed l q x:= u.grow v
lemma bare {c:ℝ} (p:∀ᶠ i in l, ‖x i‖≤c): Billed l q x:= room (BoundPoly.pureP c) p
lemma const (x:E): Billed l q (fun _=> x):= bare (Eventually.of_forall fun i=> le_refl _)
lemma tens {t:E} (f:Tendsto x l (𝓝 t)): Billed l q x:= bare (f.eventually (show ∀ᶠ x in 𝓝 t,‖x‖≤ ‖t‖+1 from (continuous_norm.continuousAt.tendsto.eventually (eventually_le_nhds (by linarith))))) -- t undeclared
lemma via (u:Billed l q x)(p:y =ᶠ[l] x) : Billed l q y:= room u (p.fun_comp norm).le
include h
lemma add (u:Billed l q x)(v:Billed l q y): Billed l q (fun i=> x i+y i):= room (BoundPoly.plusP h u v) (Eventually.of_forall fun i=> norm_add_le ..)
lemma diff (u:Billed l q x)(v:Billed l q y): Billed l q (fun i=>x i-y i):= room (BoundPoly.plusP h u v) (Eventually.of_forall fun i=> norm_sub_le ..)
lemma evol (X:ι→(E × F))(u:Billed l q (Prod.fst ∘ X))(v:Billed l q (Prod.snd ∘ X)): Billed l q X:= room (BoundPoly.plusP h u v) (Eventually.of_forall fun i=> by change max ‖(X i).1‖ ‖(X i).2‖≤_+ _; exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _)))
lemma prod1 (u:Billed l q x)(v:Billed l q y): Billed l q (fun i=>(x i,y i)):= evol h _ u v
lemma sum (X:σ→ι→E)(S:Finset σ)(v:∀ i∈ S,Billed l q (X i)): Billed l q (fun i=> ∑ j∈ S,X j i):=by
   induction S using Finset.induction_on with
   | empty=> exact via (const (0:E)) (by simp)
   | @insert i S hi ih=> exact via (add h (v i (Finset.mem_insert_self ..)) (ih (fun i j=> v i (Finset.mem_insert_of_mem j)))) (Eventually.of_forall fun a=> Finset.sum_insert hi)
lemma pi [Fintype σ] (f:ι→ σ→ E)(p:∀ i:σ,Billed l q (fun j=> f j i)): Billed l q f:=by
    have hp(S:Finset σ):BoundPoly l q (fun j=>∑ i∈ S, ‖f j i‖):= by
        induction S using Finset.induction_on with
        | empty=> exact BoundPoly.grow (BoundPoly.pureP 0) (by simp; exact Eventually.of_forall fun i=>le_rfl)
        | @insert i S v ih=> simp_rw [Finset.sum_insert v]; exact BoundPoly.plusP h (p i) ih
    refine room (hp Finset.univ) (Eventually.of_forall (fun i=> ?_)); exact (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _=>norm_nonneg _)).mpr fun j=> Finset.single_le_sum (f:=fun j=>‖f i j‖) (fun _ _=> norm_nonneg _) (Finset.mem_univ j)
lemma arrow [NontriviallyNormedField R] [ NormedSpace R E ] [NormedSpace R F] (L:E→L[R] F)(u:Billed l q x): Billed l q (fun i=> L (x i)):= room (BoundPoly.mulP h (BoundPoly.pureP ‖L‖) u (Eventually.of_forall (fun i=> norm_nonneg _))) (Eventually.of_forall fun i=> L.le_opNorm _)
omit h in
lemma root (V:ι→ℝ)(k:ℝ)(v:BoundPoly l q V)(h:0<k)(p:∀ᶠ i in l,k*‖x i‖^2≤ V i): BoundPoly l q (fun i=> k*‖x i‖^2):= v.grow p
lemma square (B:ι→ℝ)(k:ℝ)(v:BoundPoly l q B)(w:0<k)(p:∀ᶠ i in l,k*‖x i‖^2≤ B i): Billed l q x:=by
   have hx: BoundPoly l q (fun i=>‖x i‖^2):=( BoundPoly.mulP h (BoundPoly.pureP k⁻¹) (v) (p.mono (fun i hu=> le_trans (mul_nonneg w.le (sq_nonneg _)) hu)) ).grow (p.mono (fun i ht=>by change ‖_‖^ (2:ℕ)≤ k⁻¹*B i; rw [mul_comm,← div_eq_mul_inv]; exact (le_div_iff₀ w).mpr ((mul_comm ..).trans_le ht)))
   exact room (BoundPoly.plusF h hx (BoundPoly.pureP 1)) (Eventually.of_forall fun i=> by change ‖x i‖≤‖x i‖^2+1; nlinarith)
end mono
variable {x y:ι→R}[NormedField R]
include h
lemma mul (p:Billed l q x)(v:Billed l q y): Billed l q (fun i=>x i*y i):= room (BoundPoly.mulP h p v (Eventually.of_forall fun i=> norm_nonneg _)) (Eventually.of_forall fun i=> le_of_eq (norm_mul (x i) (y i)))
lemma pow (p:Billed l q x)(i:ℕ): Billed l q (fun j=> (x j)^i):=by induction i with| zero=>simpa only [pow_zero] using const (1:R)| succ i ih=>simpa only [pow_succ] using mul h ih p
lemma smul [NormedAddCommGroup E] [NormedSpace R E](f:ι→ R)(x:ι→ E)(p:Billed l q f)(v:Billed l q x): Billed l q (fun i=>f i • x i):= room (BoundPoly.mulP h p v (Eventually.of_forall fun i=>norm_nonneg _)) (Eventually.of_forall fun i=> le_of_eq (norm_smul (f i) _))
end Billed
end YM.SignedWilsonExpansion.Commission
