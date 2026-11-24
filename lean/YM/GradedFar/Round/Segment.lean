import YM.GradedFar.Round.Grid

/-!
# Value estimates, at the uniform operator price BEFORE any Gram inversion
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe Jury Facets
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (K : FramesH P)
    (θ:ℝ→ℝ) (ht:Tendsto (fun i=> θ i/gYM G i) (𝓝[>](0:ℝ)) (𝓝 1))
variable {C B:ℝ}(hC:0<C)(hB:0<B)
local notation "Q₀"=> upper G C B
local notation "Γ"=>windows Q₀
local notation "g₀"=>gYM G ∘ Window.len
include simple
set_option linter.unusedSectionVars false in
lemma w_len (v:Continuation.Window)(h:0<v.len) : v.Coarse/v.len=v.Stretch:= by change (v.len * _)/_=_; field_simp
lemma moth (a:ℝ) : ∀ᶠ (w:Continuation.Window) in Γ, w.len ≤ g₀ w ^ a := (windows_short _).eventually (Continuation.Stretch.small_root simple a)
include hC
lemma spots_span (a:ℝ) : ∀ᶠ (w:Continuation.Window) in Γ, w.Coarse ≤ C*g₀ w^a := by
    filter_upwards [windows_span Q₀, moth (simple:=simple) (C:=C) (B:=B) (a+B),(windows_short _).eventually (positive_g simple),(windows_short _).eventually self_mem_nhdsWithin] with w h hw (hp:0<g₀ w) hr

    change Window.len w * Window.Stretch w ≤ _
    apply (mul_le_mul hw h (Real.exp_pos _|>.le) (show 0≤g₀ w^(a+B) from by positivity)).trans_eq; change _*(C*g₀ w^(-B))=_; rw [rpow_neg hp.le,rpow_add hp a B]; field_simp -- h ∈Q

variable (T:Filter I)(w:I→ Continuation.Window)(hw:Tendsto w T (windows (upper G C B)))
variable {X:Set (Points n)}{Y:Set (Points m)}(hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m)
    (o:I→View U) (a:Tags G h (n+m))(S S':I→ XSet X Y)
-- already moved rounded shape to XSet X Y; budget comparison at putative corrected map here.
def ΓPath {X:Set (Points n)}{Y:Set (Points m)}(T:Filter I)(w:I→ Continuation.Window)(S S':I→ XSet X Y): Prop :=
    ∀ᶠ i in T, ∀ l∈segment ℝ (along (w i) (S i).1 (S i).2) (along (w i) (S' i).1 (S' i).2),
      ∃ x∈X,∃ y∈Y,l=along (w i) x y
variable (hy' : ΓPath T w S S')
def contour (i:I): Points (n+m):=along (w i) (S i).1 (S i).2
local notation "S₀"=>contour w S
local notation "S₁"=>contour w S'
local notation "b"=> Duly Q₀ T w hw simple
local notation "r"=> Window.len∘w
local notation "F"=> familyPoint U K h
-- Lipsprice hypotheses over path, supplied later from former
variable (D L:ℝ)(hD:0<D) (H' : ∀ᶠ (v:Continuation.Window) in windows (upper G C B), ∀ x∈X,∀y∈Y,
    ∀ o:View U,LaneCosts U K a o v.len v.Coarse x y D L)
include D L H' hD hw
-- phase need not Lips
lemma ordinary_phase : Bill (Duly Q₀ T w hw simple) p 0 (fun i=> painted U K (o i).1 (fun _=> h) ((Window.len∘w) i) (contour w S i) a -
       F (r i) (n+m) (contour w S i) a) := by
    refine ⟨D*C,mul_pos hD hC,0,?_⟩; filter_upwards [hw.eventually H',hw.eventually (spots_span (simple:=simple) hC (B:=B) ((p:ℝ)+L)),hw.eventually ((windows_short _).eventually self_mem_nhdsWithin),(Duly Q₀ T w hw simple).positive] with i hi he (hp:0<Window.len (w i)) (ht:0<g₀ (w i)); rw [post,pow_zero,neg_zero,zero_mul,exp_zero,mul_one,mul_one]
    have hi:= (hi (S i).1 (S i).1.property (S i).2 (S i).2.property (o i)).phase; dsimp only at hi; rw [w_len (simple:=simple) (w i) hp] at hi
    apply hi.trans; change D*g₀ (w i)^(-L)*_ ≤ D*C*g₀ (w i)^p
    refine (mul_le_mul_of_nonneg_left he (show 0 ≤ D*g₀ (w i)^(-L) from by positivity)).trans_eq ?_
    rw [rpow_neg ht.le,rpow_add ht,rpow_natCast]; field_simp
include hy' hX hx hY hy
variable {k':ℝ} -- actual h probing
set_option linter.unusedSectionVars false in
lemma continuous_lane (hp:(p:ℝ)+L≤ (k:ℝ)) (h : Buys T (fun i=> S₁ i-S₀ i) ((gYM G ∘ Window.len)∘w) k):
     Bill (Duly Q₀ T w hw simple) p 0 (fun i=> F (r i) _ (S₁ i) a - F (r i) _ (S₀ i) a) := by
    obtain ⟨C',hC',hk⟩:=h.exists_pos; refine ⟨D*C',mul_pos hD hC',0,?_⟩
    have hc :=eventually_conf hX hx hY hy
    filter_upwards [hk.bound,hw.eventually H',hw.eventually ((windows_separation _).eventually hc),hw.eventually ((windows_short _).eventually self_mem_nhdsWithin),hy',(Duly Q₀ T w hw simple).positive,(Duly Q₀ T w hw simple).shrinking.eventually_lt_const zero_lt_one] with i hi he hz (hr:0<Window.len (w i)) path (ht:0<g₀ (w i)) (hw':g₀ (w i)<1)
    let V t:= F (r i) _ t a; let P := segment ℝ (S₀ i) (S₁ i); let D' :=D*g₀ (w i)^(-L)
    have hf t (hp:t∈P): DifferentiableAt ℝ V t := by obtain ⟨x,hx,y,hy,rfl⟩:=path _ hp; have hh:=hz.1 x hx y hy; rw [wide_here] at hh; exact fit_gradient U K none _ _ (present hr hh)
    have hF t (hp:t∈P) : ‖fderiv ℝ V t‖ ≤ D' := by
      obtain ⟨x,hx,y,hy,rfl⟩:=path _ hp; have hh:=(he x hx y hy (none,0)).rate; rw [w_len (simple:=simple) _ hr] at hh; exact hh
    change _ ≤ C'*‖g₀ (w i)^k‖ at hi
    rw [Real.norm_of_nonneg (pow_nonneg ht.le k)] at hi
    rw [post,pow_zero,neg_zero,zero_mul,exp_zero,mul_one,mul_one]
    apply ((convex_segment ..).norm_image_sub_le_of_norm_fderiv_le hf hF (left_mem_segment ..) (right_mem_segment ..)).trans
    change D*g₀ (w i)^(-L)*_ ≤D*C'*g₀ (w i)^p
    apply (mul_le_mul_of_nonneg_left hi (show 0 ≤ D*g₀ (w i)^(-L) from by positivity)).trans; have hz:= Real.rpow_le_rpow_of_exponent_ge ht hw'.le hp
    rw [Real.rpow_add ht,Real.rpow_natCast,Real.rpow_natCast] at hz; let t:=g₀ (w i)
    calc
     _ ≤ D*t^(-L)*(C'*(t^p*t^L)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hC'.le) (by change 0≤D*t^(-L); have he:0<t:=ht; positivity)
     _ = _ := by change _=D*C'*t^p; rw [rpow_neg (show 0≤t from ht.le)]; have h:0<t:=ht; field_simp
omit hC D L H' hD
include H
lemma derivative_lane (h : Buys T (fun i=> S₁ i-S₀ i) (g₀∘w) p) (j:ℕ) : Bill (Duly Q₀ T w hw simple) p 0 (fun i=> ranker N j a (S₁ i)-ranker N j a (S₀ i)) := by
    obtain ⟨C,hC,h'⟩:= h.exists_pos
    obtain ⟨D,hD,k,H'⟩:= rate N M H hX hx hY hy a j
    refine ⟨C*D,mul_pos hC hD,k,?_⟩

    filter_upwards [h'.bound,hw.eventually ((windows_separation _).eventually H'), hw.eventually ((windows_separation _).eventually (eventually_conf hX hx hY hy)),hy',hw.eventually ((windows_separation _).eventually_ge_atTop 0), hw.eventually ((windows_short _).eventually (positive_g simple))] with i hi H' he path hv ht
    let P:=segment ℝ (S₀ i) (S₁ i); let L:=D*post 0 (Window.sep (w i)) k
    have hf t (hp:t∈P) : DifferentiableAt ℝ (ranker N j a) t := by obtain ⟨x,hx,y,hy,rfl⟩:=path _ hp; have hh:=he.1 x hx y hy; rw [wide_here] at hh; exact smooth_sail N M H j a hh
    have hL t (hp:t∈P) : ‖fderiv ℝ (ranker N j a) t‖ ≤ L := by
      obtain ⟨x,hx,y,hy,rfl⟩:=path _ hp; have hh:= H' ((⟨x,hx⟩,⟨y,hy⟩):XSet X Y); rw [to_along] at hh; exact hh
    change _ ≤ C*‖g _^p‖ at hi; rw [Real.norm_of_nonneg (pow_nonneg ht.le p)] at hi
    apply ((convex_segment ..).norm_image_sub_le_of_norm_fderiv_le hf hL (left_mem_segment ..) (right_mem_segment ..)).trans
    exact (mul_le_mul_of_nonneg_left hi (mul_nonneg hD.le (post_at hv).le)).trans_eq (by change L*_ = C*D*g _^p*post 0 (Window.sep (w i)) k; unfold L; ring)
include ht
lemma eval_lane (h : Buys T (fun i=> S₁ i-S₀ i) (g₀∘w) p) (j:ℕ) :
    Bill (Duly Q₀ T w hw simple) p 0 (fun i=> crop j (θ (r i)) (boundary N a (S₁ i)) - crop j (θ (r i)) (boundary N a (S₀ i))) := by
    simp only [crop_eq]; simp_rw [←Finset.sum_sub_distrib,← mul_sub]
    have hh : ∀ᶠ i in (Duly Q₀ T w hw simple).l, |θ (r i)| ≤ 2*(Duly Q₀ T w hw simple).g i:= (((windows_short _).comp hw).eventually (paid_reading simple θ ht)).mono fun i h=>h.2.2.2
    refine Bill.sum _ (fun j _=>?_); simpa only [zero_add,ranker,comp_apply] using ((Ledger.exponent (t:=θ ∘ r) hh j).mono_fee (v:=0) le_rfl (Nat.zero_le j)).times (derivative_lane N M H T w hw hX hx hY hy a S S' hy' h j)
end
end YM.FVA2.GradedFar.Physical.Round
