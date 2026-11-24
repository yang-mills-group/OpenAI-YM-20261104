import YM.Contacts.Loom.Kiosk
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Capture
open PertExtension.Series Radial Milling
variable {n h:ℕ}[∀ i,FiniteDimensional ℝ (F i)] {W:Lamp F}{d g:ℕ→ℝ}{u:Shelf E α F}{x:Frame α E} {s:ℝ}
def stashp := -(41/100:ℝ)
def fit := -(21/50:ℝ)
def race := -(1/5:ℝ)
variable (hp:Root N W k 0 d) (hr:Pouch N stashp d)(hg:Pouch N (-(1/2)) g) (hv : Budget N x k fit u)

def pulse (S:Lamp F)(g:ℕ→ℝ)(u:Shelf E α F): Mint E α:= fun i j x=>-((g i)⁻¹^2)* (S i - skel (S i) 3) (u i j x)
lemma sees_radius (r:ℕ)(he:r≠0)(i:ℕ)(j:α i)(t:E i)(hx:g i≠0): codes W g u r i j t= -((g i)⁻¹^2)*jet (W i) (r+2) (u i j t):= by
   rw [codes,Radial.layers,if_neg he,add_zero, jet_smul,pow_add,inv_pow]; field_simp
lemma pleasure (i:ℕ)(hx:g i≠0): (pulse W g u - green (codes W g u) n) i = fun j=> -((g i)⁻¹ ^ 2) • ((W i-skel (W i) (n+3))∘ u i j) := by
   induction n with
   | zero=>rw [green,Finset.sum_range_one,codes_omit,sub_zero]; rfl
   | succ n ih=>
      set z:=pulse W g u; set p:=codes W g u; rw [show green p (n+1)=green p n + p (n+1) from Finset.sum_range_succ .., sub_add_eq_sub_sub]; funext j t; erw [Pi.sub_apply,ih]; change -_*_ - codes _ _ _ _ _ _ _ = -((g i)⁻¹^2)* _; rw [sees_radius (n+1) (by omega) _ _ _ hx]; simp only [Function.comp_apply,Pi.sub_apply]; unfold skel; rw [show n+1+3=n+3+1 from by omega,Finset.sum_range_succ _ (n+3)]; rw [show n+1+2=n+3 from by omega]; ring
include hp hr hg hv
lemma book (he:n+3≤k): Word N x k n race (pulse W g u) (codes W g u):= by
   have ht : N.Rush (1:ℝ) fun i=>-((g i)⁻¹^2):= by
      have h:= (YM.Contacts.Loom.Rush.absSq hg.back).multiplier (-1); norm_num at h; simpa only [inv_pow] using h
   have hh := hr.bank hv (by norm_num [stashp,fit])
   let θ:=race; refine ⟨by norm_num [race],fun i hi=>?_ ,?_⟩
   · have ht' := he; by_cases hz:i=0; · rw [hz,codes_omit]; exact Budget.zero
     have hc:= hp.worth hr (Nat.le_trans (Nat.add_le_add_right hi 2) (by omega))
     refine ( (Arms.weighted (Budget.jetcap hv hc) ht rfl) |>.reveal ?_ ?_ le_rfl)
     · exact hg.pos.mono fun k hk i'=> Eventually.of_forall fun x'=>sees_radius i hz k i' x' hk.ne'
     unfold race fit; push_cast; have hx: (1:ℝ)≤ (i:ℝ):=(by exact_mod_cast (show 1≤ i from Nat.one_le_iff_ne_zero.mpr hz)); linarith only [hx]
   let m i:= (W i-skel (W i) (n+3)); have hs:= Root.application (S:=m) ((hp.reminder hr he (by norm_num [stashp]))) hh hr hv (by norm_num [fit,stashp]); refine Arms.confirm (h:=?_ ) ((Arms.weighted hs ht rfl).lo ?_ le_rfl) -- order
   · exact hg.pos.mono fun i hi=> pleasure i hi.ne'
   unfold race stashp; push_cast; have h:= Nat.cast_nonneg (α:=ℝ) n; linarith only [h]
omit hp hr hg hv in
lemma same_values {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](T:V→ℝ)(g:ℝ)(x:V)(hg:g≠0)(hf:jet T 0 x=0 ∧jet T 1 x=0) : higher T g (g⁻¹ • x)= -(g⁻¹^2)*(T x-skel T 3 x):= by
     unfold higher; rw [smul_inv_smul₀ hg,jet_smul,skel]; simp only [sum_range_succ, Finset.range_zero,Finset.sum_empty,hf.1,hf.2]; field_simp; ring
lemma rotor (he:n+3≤k)(hx: race<q)(hy:q<0): Word N x k n q (expn (pulse W g u)) (rol (codes W g u) n):= (book hp hr hg hv he).active (codes_omit W g u) hx hy
end Capture
end
end YM.Contacts.Loom
