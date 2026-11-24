import YM.Contacts.Model.Scroll
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals Stationary Milling PertExtension.Series Exterior Precision Ion
open Push.Uniform Work.F02 Metric Radial
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n m c:Side}{k w r:ℕ}
variable {Z μ C Λ:ℝ}{p:Clip}{R:PathData G}
section expenses
variable (x:Site m) (F : ℕ→Atom G r)
variable {K:Type}[NormedAddCommGroup K][NormedSpace ℝ K]{U:K → Config G m}{y:K}{X:Set K}
variable (hO:IsOpen X)(hc:IsPreconnected X)(hx: y∈ X) (ht:∀ i z, z∈X→Allows k (fun y=> G.mat (U y i)) z Z)
include hO hc hx ht
def tiny (F:ℕ→Atom G r)(w:ℕ): Story G:= stem F (part (fun i=> (F i).length) w)
lemma twig (w:ℕ)(hs:0<μ)(hf:SumBudget (fun i=>(F i).budget μ) C) : Allows k (pass (stem F Set.univ) m x ∘ U - pass (tiny F w) m x ∘ U) y ((pole μ w * C)*atomSize G μ Z k r) := by
   let V:=part (fun i=> (F i).length) w; let a:=stem F Set.univ; let S:= Vᶜ
   have hh W: pass a m x W=pass (tiny F w) m x W+ title S x F W:= by
     rw [show pass a m x W=_ from (tsum_subtype_eq_of_support_subset (s:=Set.univ) (f:=fun i=> (F i).unmasked W x) (Set.subset_univ _) : pass a m x W=_)]; exact Eq.symm (Summable.tsum_add_tsum_compl (s:=V) ((grains x F hs hf W).subtype _) ((grains x F hs hf W).subtype _))
   apply Allows.germ (yore S x hO hc hx ht F hs hf w (fun i hi=> le_of_lt (lt_of_not_ge hi))); exact Eventually.of_forall (fun i=>by change _= pass a m x _ - _; rw [hh]; change _= (_+_) - pass (tiny F w) m x (U i); abel)
variable (R p)
-- mask represented by either exact (none) or integer q≥4. Charge by charge

def deep (w:Option ℕ): Story G:= (fire R p (w.elim (fun _=> Set.univ) fun w i=> part (pullLength R i) w))+(w.elim (stem R.cubic Set.univ) (tiny R.cubic))+(w.elim (stem R.quartic Set.univ) (tiny R.quartic))
def ocean (w : Option ℕ): Story G:= w.elim (stem R.loop Set.univ) (tiny R.loop)
def boats (w:Option ℕ)(i:ℕ): Story G:= if i=0 then deep p R w else if i=2 then ocean R w else 0 -- order
omit hO hc hx ht in
lemma train (V:Story G)(hv:∀ i, Allows k (pass V m i ∘ U) y C): Allows k (froth (pass V m) ∘ U) y (Fintype.card (Site m)*C):= by have hx:= allows_sum (s:=univ) fun i _=> hv i; rw [Finset.sum_const,nsmul_eq_mul,card_univ] at hx; exact hx
variable (h : R.Bounds p μ C Λ)
def quadTip (G:Gauge)(p:Clip)(Z μ C:ℝ)(k:ℕ):= (Fintype.card PlaqAxes:ℝ)*(|p.direct| * priceCost G (travelCost G k 4 Z)+(1/2)*(2^k:ℝ)*(C*portSize G μ Z k)^2)
def sumFee (G:Gauge)(p:Clip)(Z μ C Λ:ℝ)(k:ℕ) := |quadTip G p Z μ C k|+|C*atomSize G μ Z k 3|+|C*atomSize G μ Z k 4|+|Λ*atomSize G μ Z k 2|+ (Fintype.card PlaqAxes:ℝ)*((2^k:ℝ)*(2*(C*portSize G μ Z k)^2))
omit hO hc hx ht in
lemma sumFee_nn : 0≤ sumFee G p Z μ C Λ k:=by unfold sumFee; positivity
include h
lemma badgeP (V:Option ℕ)(i:ℕ) : Allows k (pass (boats p R V i) m x ∘ U) y (sumFee G p Z μ C Λ k):= by
   let Q:= sumFee G p Z μ C Λ k; have he F:= highPair hO hc hx ht F x h; have ha (z:ℕ)(F:ℕ→Atom G z)(C':ℝ)(h':SumBudget (fun i=>(F i).budget μ) C') : Allows k (pass (V.elim (stem F Set.univ) (tiny F)) _ x ∘ U) y (C'*atomSize G μ Z k z):= by
      have hb (b:Set ℕ): Allows k (title b x F ∘ U) y (C'*atomSize G μ Z k z):= by simpa only [Model.pole,Nat.cast_zero,mul_zero, Real.exp_zero,one_mul] using yore b x hO hc hx ht F h.width h' 0 (fun _ _=> Nat.zero_le _)
      cases V <;> exact hb _
   have hx : 0≤ (Fintype.card PlaqAxes:ℝ)*(2^k*(2*(C*portSize G μ Z k)^2)):= by positivity
   unfold boats; split
   · refine (((he _).add (ha _ _ C h.three)).add (ha _ _ C h.four)).mono ?_; change quadTip G p Z μ C k+_+_ ≤ _; unfold sumFee; have h (x:ℝ):=le_abs_self x; linarith only [h (C*atomSize G μ Z k 3),h (C*atomSize G μ Z k 4), h (quadTip G p Z μ C k),hx,abs_nonneg (Λ*atomSize G μ Z k 2)] -- inspect
   split; next _=> exact (ha _ R.loop _ h.two).mono (by apply le_trans (le_abs_self _); unfold sumFee; linarith [abs_nonneg (quadTip G p Z μ C k),abs_nonneg (C*atomSize G μ Z k 3),abs_nonneg (C*atomSize G μ Z k 4)])
   exact allows_const y (v:=(0:ℝ)) (show ‖(0:ℝ)‖≤ _ from (norm_zero (E:=ℝ)).trans_le (sumFee_nn p))
lemma copyP (w:ℕ)(i:ℕ) : Allows k (pass (boats p R none i) m x ∘ U- pass (boats p R (some w) i) m x ∘ U) y (pole μ w*sumFee G p Z μ C Λ k):= by
   let W (f:Story G):= pass f _ x ∘ U; let q:= W (boats p R none i) - W (boats p R (some w) i)
   have ht'(x:ℝ):=le_abs_self x
   have hK: 0≤pole μ w:= (Real.exp_pos _).le
   unfold boats; split
   next _=> apply Allows.germ (((((fault_booth w hO hc hx ht h x).add (twig x R.cubic hO hc hx ht w h.width h.three)).add (twig x R.quartic hO hc hx ht w h.width h.four)).mono ?_)); swap
            · calc _ = pole μ w*((Fintype.card PlaqAxes:ℝ)*(2^k*(2*(C*portSize G μ Z k)^2))+C*atomSize G μ Z k 3+C*atomSize G μ Z k 4):= by ring
                   _ ≤ _:= mul_le_mul_of_nonneg_left (by unfold sumFee; linarith only [ht' (C*atomSize G μ Z k 3),ht' (C*atomSize G μ Z k 4), abs_nonneg (quadTip G p Z μ C k),abs_nonneg (Λ*atomSize G μ Z k 2)]) hK
            · exact Eventually.of_forall (fun i=> by dsimp only [deep,Pi.add_apply,Pi.sub_apply,pass, Function.comp_apply, Option.elim] ; abel)
   split
   next _=>
     refine (twig x R.loop hO hc hx ht w h.width h.two).mono ?_
     have he:=abs_nonneg (C*atomSize G μ Z k 3); have hv:0≤ (Fintype.card PlaqAxes:ℝ)*(2^k*(2*(C*portSize G μ Z k)^2)):= by positivity
     rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hK; unfold sumFee; linarith only [ht' (Λ*atomSize G μ Z k 2), he, abs_nonneg (C*atomSize G μ Z k 4),abs_nonneg (quadTip G p Z μ C k), hv]
   rw [sub_self]; exact allows_const y ((norm_zero (E:=ℝ)).trans_le (mul_nonneg hK (sumFee_nn p)))
end expenses
end YM.Contacts.Model
