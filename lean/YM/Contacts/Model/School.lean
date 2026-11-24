import YM.Contacts.Model.Twig
/-! Assessment tools for individual loop-power heights. Sym cover alignment.
 Doesn't assert accounting in clocks alone. Different Side all. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals Stationary Milling PertExtension.Series Exterior Precision Ion
open Push.Uniform Work.F02 Metric Radial
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical NNReal InnerProductSpace
variable {G:Gauge}{n m c:Side}{k w r:ℕ}
variable {Z μ C Λ:ℝ} (p:Clip)(R:PathData G)

lemma addsHome (Q V : Story G): froth (pass (Q+V) m)= froth (pass Q m)+froth (pass V m):= by ext x; simp only [froth,pass,Pi.add_apply,Finset.sum_add_distrib]
def base (m:Side)(i:ℕ) : Config G m→ℝ:= if i=0 then mainTerm p R else if i=2 then Precision.loop R else 0
lemma uses (i:ℕ): froth (pass (hue (boats p R none i)) m)= base p R m i:= by
    ext x; rw [from_home]; unfold boats base; split
    · change VerifiedReset.factor *_=Patch.average _; apply congr_arg; apply sum_congr rfl; intro i _; change froth (pass (fire R p _ + stem R.cubic _ + stem R.quartic _) m) _= quadratic _ _ _ + Precision.uncut _ _ + Precision.uncut _ _; rw [addsHome,addsHome]; simp only [Pi.add_apply]; exact congr_arg₂ (·+·) (congr_arg₂ (·+·) (bright ..) (starview ..)) (starview ..) -- metavars annotations
    split; next h=> apply congr_arg (VerifiedReset.factor * ·); exact sum_congr rfl fun i _=> starview R.loop _ -- adjust
    simp [pass,froth]
lemma resides (hw:4≤w)(i:ℕ): LocalOn (Lattice.box w) (hue (boats p R (some w) i)):= by
    apply hue_loc; unfold boats; split
    · intro x v h; exact congr_arg₂ (·+·) (congr_arg₂ (·+·) (scroll_fire R p hw x v h) (scroll_stem R.cubic w x v h)) (scroll_stem R.quartic w x v h)
    split; next _=> exact scroll_stem R.loop w
    exact fun _ _ _=>rfl
-- pay practical log estimates with gross masses
lemma outerBrush {K:Type}[NormedAddCommGroup K][NormedSpace ℝ K]{U:K → Config G m}{y:K}{X:Set K} (hO:IsOpen X)(hc:IsPreconnected X)(hx: y∈ X) (ht:∀ i z, z∈X→Allows k (fun y=> G.mat (U y i)) z Z)(V:Option ℕ)(x:Site m)(h:R.Bounds p μ C Λ)(i:ℕ) : Allows k (pass (hue (boats p R V i)) m x ∘ U) y (sumFee G p Z μ C Λ k):= by
    let f z a:= pass (boats p R V i) m (a⁻¹.act x) (pull a 0 (U z)); change Allows k _ _ _; unfold Function.comp; simp_rw [citizen_hue];
    let V a z:= pull a (0:Site m) (U z)
    apply allows_average (f:=fun a z=> f z a); intro a; refine badgeP p R (a⁻¹.act x) (U:=V a) hO hc hx ?_ h _ i; intro j z hz; unfold V pull Lattice.Step.read; split; next _=> exact (ht _ _ hz).inverse (f:=fun z=> _)
    exact ht _ _ hz
lemma sand_bar (Z:Option ℕ)(h:R.Bounds p μ C Λ) (i:ℕ)(x:Site m): altitude (pass (boats p R Z i) m x):= by
  obtain ⟨T,hT⟩:= paint_supply G 0
  exact ((badgeP (k:=0) p R x isOpen_ball (convex_ball _ _).isPreconnected (mem_ball_self (x:=(0: Link G m)) zero_lt_one) (fun i z h=>imprints hT (mem_ball_zero_iff.mp h).le i) h Z i).analytic).analyticAt
lemma averageFault {α:Type*}[Fintype α](f g:α→ℝ)(h:∀ i, ‖f i-g i‖ ≤ Z) : ‖(∑ i,f i)-(∑ i,g i)‖ ≤ (Fintype.card α:ℝ)*Z := by
  rw [← sum_sub_distrib]; exact (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>Z) (fun i _=>h i)).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ]))
lemma jet_suff {f:Link G n→ℝ}{g:Link G n→ℝ}(hx: AnalyticAt ℝ f 0)(hf: AnalyticAt ℝ g 0)(h:Allows k (f-g) 0 Z)(x:Link G n): ‖jet f k x-jet g k x‖ ≤ Z*‖x‖^k := by
  rw [← Ion.jet_minus _ _ _ _ hx hf]; unfold jet; rw [norm_mul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_);
  · have hh:= ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ k (f-g) 0) (fun _=>x); simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh; exact hh.trans (mul_le_mul_of_nonneg_right (h.norm_le _ le_rfl) (pow_nonneg (norm_nonneg _) _))
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ ((k.factorial:ℝ)⁻¹))]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos k)
lemma silt (hZ:PaintSupply G k Z)(h:R.Bounds p μ C Λ)(w:ℕ)(x:Link G m)(i:ℕ) : ‖jet (base p R m i ∘ input G m) k x - jet (plays (pass (hue (boats p R (some w) i)) m)) k x‖ ≤ (Fintype.card (Site m):ℝ)* (pole μ w*sumFee G p (outerCost G k Z) μ C Λ k)*‖x‖^k := by
   rw [← uses]; let C':=pole μ w*sumFee G p (outerCost G k Z) μ C Λ k; have hz:0≤C':= mul_nonneg (Real.exp_pos _).le (sumFee_nn p); let f t:= boats p R t i; let g (t:Option ℕ):= plays (pass (f t) m)
   erw [show jet (plays (pass (hue (boats p R none i)) m)) k x= _ from breeze (sand_bar p R none h i) x k,breeze (sand_bar p R (some w) h i) x k]; rw [← mul_sub,norm_mul]
   have hv s : ‖jet (g none) k (orderTurn s x)-jet (g (some w)) k (orderTurn s x)‖ ≤ (Fintype.card (Site m):ℝ)*C'*‖x‖^k:= by
      let v (t:Option ℕ)(x:Site m):=pass (f t) m x ∘ input G m; have hs t x:AnalyticAt ℝ (v t x) 0:= sand_bar p R t h i x; let q := orderTurn s x; have he y : Allows k (v none y-v (some w) y) 0 C':= copyP p R y isOpen_ball (convex_ball _ _).isPreconnected (mem_ball_self (x:=(0: Link G m)) zero_lt_one) (fun a z h=>imprints hZ (mem_ball_zero_iff.mp h).le a) h w i;
      have hx t:jet (g t) k q=∑ i:Site m,jet (v t i) k q:= loan_sum univ (fun i _=> hs t i) k _; rw [hx,hx,mul_assoc]; exact averageFault _ _ (fun i=> (jet_suff (hs _ _) (hs _ _) (he i) q).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q) (shape_invoice s x) _) hz))
   rw [Real.norm_of_nonneg VerifiedReset.factor_pos.le]; apply le_trans (mul_le_mul_of_nonneg_left (averageFault _ _ hv) VerifiedReset.factor_pos.le); rw [←mul_assoc,VerifiedReset.factor_card,one_mul]
end YM.Contacts.Model
