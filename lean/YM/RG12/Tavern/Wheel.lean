import YM.RG12.Strike.Recipes
import YM.RG12.Alidade.Contract
/-! # Less information than a full infinitesimal stabilizer test suffices.

In a normalized SCHEME frame: assume two-order formal group response on positions
on JUST THESE PAIR configurations with no grade change under scale group (scheme obligation,
e.g. computed normalized formal prescription required, not from the thermal lattice).
Given this law we needn't prove there is NO O(g) field-scale generator as map (which would need
information from multiple other arities). Our rigorous Taylor coefficient law on pointwise
pairs alone KILLS the O(g) response on reflected-price INCLUDING all spin mixing.
Polarization recovers only ON THESE PAIRS the skewness of the first generator; that suffices
also on the SECOND-order common response: the dangerous (log ratio)^2
amplification through unbounded L_j cancels along the flow EVEN if a first-order
rotation remains. All calibration changes for physical projection can be priced with these
weaker requirements. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Tavern
open Frames Alidade Function Filter Set Real Finset
open scoped Topology BigOperators Classical
variable {d:ℕ}{V:Grade d→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)]
set_option quotPrecheck false
local notation "A!"=>Col V
open Strike
-- argument t≥1 is length dilation, INSERTION bases at scale 1 (and dilation on
-- insertion inputs ALREADY within T, so T(t) is usual coordinate-space scheme report
-- evaluated at e positions and engineered fields). Flow data only formal.
structure Wheel (V:Grade d→Type)[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)] where
    C : Charge (V:=Col V)
    movement : Mixes (V:=Col V) -- generator coefficients b1,b2
    X : ℝ→ Charge (V:=Col V)
variable (Q:Wheel V)(K:ℝ)
local notation "Y0"=>Q.C.zeroth.val
local notation "Y1"=>Q.C.first.val
local notation "Y2"=>Q.C.second.val
local notation "B1"=> Q.movement.first
local notation "B2"=> Q.movement.second
-- finite normalized group data through two orders. beta_g must have no quadratic in this
-- chosen input (other schemes can supply slightly different input or prove conversion).
-- smoothing cond: minimum probes required. only these T orientations; Ward/source comparator
-- on other configurations not consumed here. `pointwise` real-projected, accepts arbitrary
-- amplitude recipe at chosen lifted fields, even symmetrizations inheriting explicit Ward
-- additions. May disestablish FrameName identification separately.
structure Weather :Prop where
    prices : Nonempty (Casket Q.C Q.movement K)
    pounds (x:A!): ‖x‖^2 ≤ K*Y0 x x
    symmetry (x y:A!): Y0 x y=Y0 y x
    flow (t:ℝ)(ht:1≤t): ∀ x:A!,
       let b:=Real.log t; let T:=Q.X t; let u:=B1 x; let v:=B2 x; let w:=B1 u
       T.zeroth.val x x=Y0 x x ∧
       T.first.val x x=Y1 x x + b*(Y0 u x + Y0 x u) ∧
       T.second.val x x=Y2 x x+b*(Y0 v x+Y0 x v+Y1 u x+Y1 x u)+b^2*(Y0 u u+(Y0 w x+Y0 x w)/2)
    -- continuum Taylor prediction in symmetrically projected pair coefficients (S mirror convention
    -- & Gram eval already INCLUDED): for each configuration j in these oriented tests,
    -- any formulation that collects into `First` readings with constant shifts qualifies. We
    -- require representation on arbitrary small open comparison interval, NOT analytic
    -- continuation down to zero. Colors/spin signs, normalization P_b etc must agree in supplying
    -- these scalar coeffs. Equivalent coefficients at lattice-regulator & thermal theory not
    -- supplied here. x & y are arbitrary components of grading, not just probes themselves.
    pointwise (i j:Grade d) (x:V i)(y:V j):
        let p:=i.val+j.val
        ∃ (z:Strike.R) (f:Strike.R→ℂ) (T:ℝ), z≠0 ∧ 1<T∧ First p f ∧ ∀ t:ℝ,1 ≤ t→t<T →
        (Q.X t).first.val (Frames.put V i x) (Frames.put V j y)=(((t:ℂ)^p * f (t • z))).re
    symAt t (ht:1≤t) (x y:A!): (Q.X t).first.val x y = (Q.X t).first.val y x
    symOne (x y:A!) : Y1 x y = Y1 y x

-- pass to re Waive (identified via ℂ due `no_coupon`)
lemma washed {d}{x:ℝ→ℂ}(H:Waive d x):Waive d (fun y=>((x y).re:ℂ)):=by
   obtain ⟨c,hc⟩:=H; refine ⟨fun i=>((c i).re:ℂ),fun y hy=>?_⟩; dsimp only; rw [hc y hy,Complex.re_sum,Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i hi
   rw [← Complex.ofReal_pow,← Complex.ofReal_one, ←Complex.ofReal_sub,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,Complex.ofReal_mul]
variable {Q K} (h:Weather Q K)
include h
lemma mason t (ht:1≤t)(x y:A!) : (Q.X t).first.val x y=Y1 x y+Real.log t*(Y0 (B1 x) y + Y0 x (B1 y)):=by
    have h₀:= (h.flow _ ht x).2.1
    have h₁:= (h.flow _ ht y).2.1
    have hv:= (h.flow _ ht (x+y)).2.1
    simp only [Tile.add,Tile.add',map_add,h₀,h₁,h.symAt _ ht y x,h.symOne y x,h.symmetry y (B1 x), h.symmetry (B1 y) x] at hv
    linarith
lemma funding (i j:Grade d)(x:V i)(y:V j): let a:= Frames.put V i x; let b:= Frames.put V j y; Y0 (B1 a) b + Y0 a (B1 b) = 0:=by
   intro a b; let c:= Y0 (B1 a) b+ Y0 a (B1 b)
   obtain ⟨z,f,T,hz,hT,hf,hX⟩:=h.pointwise i j x y
   let p:=i.val+j.val; have ht := exacted z hz hf
   let k:=(-(c:ℂ)); have hv:k=0:=by
     refine no_coupon _ (washed ht) hT fun t he=>?_
     have h1:= (hX _ he.1.le he.2).symm.trans (mason h t he.1.le a b)
     have hh:= (hX _ (le_rfl (a:=1)) hT).symm.trans (mason h 1 (le_rfl (a:=1)) a b)
     simp only [Real.log_one,one_smul,Complex.ofReal_one,one_pow,one_mul, zero_mul,add_zero] at hh
     change ((Gap z p f t).re:ℂ)=_
     unfold Gap;unfold k c;rw [Complex.sub_re,h1,hh]; push_cast; ring 
   change c=0; exact_mod_cast neg_eq_zero.mp hv

lemma both (x y:A!): Y0 (B1 x) y+ Y0 x (B1 y)=0:=by
   let S(a b:A!):=Y0 (B1 a) b+Y0 a (B1 b)
   have hh (x:A!):=Frames.by_grade V x
   have h₁(x v y:A!):S x (v+y)=S x v+S x y:=by unfold S; rw [map_add,Tile.add',Tile.add']; ring
   have h₂(x v y:A!):S (v+y) x=S v x+S y x:=by unfold S;rw [map_add,Tile.add,Tile.add];ring
   have he(f:A!→ℝ)(hf:∀ x y,f (x+y)=f x+f y)(x:Col V): f x=∑ i,f (Frames.put V i (x i)):=by
      conv_lhs=>rw [←hh x]
      suffices h:∀ (s:Finset (Grade d)) (a:Grade d → Frames.Col V), f (∑ i∈s,a i)=∑i∈s,f (a i) from h Finset.univ _
      intro s a; induction s using Finset.cons_induction_on with
      | empty=> have h':0+(0:A!)=0:=add_zero _;have h:= (hf (0:A!) (0:A!));rw [h'] at h;simp only [Finset.sum_empty]; linarith
      | cons i p hi hv=> rw [sum_cons,sum_cons,hf,hv]
   change S x y=0;rw [show S x y=_ from he (fun a=>S a y) (h₂ y) x]; apply sum_eq_zero;intro i _;let v:=Frames.put V i (x i);rw [he (S v) (h₁ v)];exact sum_eq_zero fun j _=>funding h _ _ _ _

lemma sheared (t:ℝ)(ht:1≤t) (x:A!):
    let T:=Q.X t; T.first.val x x=Y1 x x ∧
    |T.second.val x x-Y2 x x| ≤4*K^2* Real.log t* ‖x‖^2 :=by
   dsimp only
   have hh:=both h x x;have hw:= (h.flow t ht x).2
   let v:=B1 x;let w:=B2 x; let A:=Y0 v v
   have ha:2*A+Y0 (B1 v) x+Y0 x (B1 v)=0:=by
      linarith only [both h x v,both h v x]
   constructor
   · rw [hw.1,hh,mul_zero,add_zero]
   rw [hw.2,add_assoc,add_sub_cancel_left] --?? target abs. 
   obtain ⟨H⟩:=h.prices; let u:=‖x‖; have h0 :0≤K:=zero_le_one.trans H.hex
   have hT {b:A!}{P:A!→A!→ℝ}(hz:‖b‖ ≤ K*u)(hf:∀ x y, |P x y| ≤ K*‖x‖*‖y‖): |P x b| ≤ K^2*u^2 := (hf x b).trans (by grw [hz];unfold u; rw [sq K,sq ‖x‖]; ring_nf; exact le_rfl)
   have hT' {b:A!}{P:A!→A!→ℝ}(hz:‖b‖ ≤ K*u)(hf:∀ x y, |P x y| ≤ K*‖x‖*‖y‖): |P b x| ≤ K^2*u^2:= hT (P:=fun x y=>P y x) hz (fun i j=> by apply (hf j i).trans; ring_nf; exact le_rfl)
   have ht' :0 ≤ Real.log t:=Real.log_nonneg ht
   have hx : A+(Y0 (B1 v) x+Y0 x (B1 v))/2=0:=by linarith
   change |Real.log t*(_)+ (Real.log t)^2 * (A+(Y0 (B1 v) x+Y0 x (B1 v))/2)| ≤ _
   rw [hx,mul_zero,add_zero,abs_mul,abs_of_nonneg ht']
   calc _ ≤ Real.log t*(4*(K^2*u^2)) :=by gcongr; linarith only [abs_add_le (Y0 w x+Y0 x w+Y1 v x) (Y1 x v),abs_add_le (Y0 w x+Y0 x w) (Y1 v x),abs_add_le (Y0 w x) (Y0 x w),hT (H.a x) H.zero,hT' (H.a x) H.zero,hT (H.h x) H.one,hT' (H.h x) H.one]
        _ = _:=by unfold u; ring
end YM.RG12.Tavern
