import YM.Contacts.Model.Voyage
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals Stationary Milling PertExtension.Series Exterior Precision Ion
open Push.Uniform Work.F02 Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n m c:Side}{k w r:ℕ}
variable {Z μ C Λ:ℝ}{p:Clip}{R:PathData G}
variable (R) (a:PlaqAxes)
def part (p:ℕ→ℕ)(w:ℕ) : Set ℕ:= { i| p i ≤ w}
def glow (V:Set ℕ) (U:CoverConfig G):G.Color:= ∑' i:↥V, (R.row a i.val).1 • (R.row a i.val).2.eval U
def fire (p:Clip)(V:PlaqAxes→Set ℕ): Story G := fun U=> ∑ a:PlaqAxes, (p.direct * orig a U + ‖Model.glow R a (V a) U‖^2/2)
-- fix ∑ precedence
-- atom section
def stem (F:ℕ→Atom G r)(V:Set ℕ): Story G:= fun U=> ∑' i:↥V,Stationary.aTerm (F i.val) U
private lemma scroll_mon {A B:Set Cover}{U V:CoverConfig G}(h:Agrees B U V)(he:A⊆ B): Agrees A U V:= fun i hi hh=> h i (he hi) (he hh)
lemma scroll_stem (F:ℕ→Atom G r)(w:ℕ) : LocalOn (Lattice.box w) (stem F (part (fun i=> (F i).length) w)):= by
    intro U V h; refine tsum_congr fun i=> Stationary.aTerm_at (F i.val) U V (scroll_mon h ?_)
    have hl:(F i.val).length≤w:= i.property; intro z hz; obtain ⟨hX,hV⟩:= box_test.mp (Finset.mem_coe.mp hz); exact box_test.mpr ⟨fun i=>by have hx:=hX i; omega,fun i=>by have hv:=hV i; omega⟩
lemma scroll_glow (w:ℕ) : LocalOn (Lattice.box w) (Model.glow R a (part (pullLength R a) w)):= by
    intro U V h; refine tsum_congr fun i=> congr_arg ((R.row a i.val).1 • ·) ((R.row a i.val).2.covered U V (scroll_mon h ?_)); intro z hz; apply scene_lt; exact (slot_weight _ hz).trans i.property -- locate power cons
lemma scroll_fire (p:Clip)(hw:4≤w) : LocalOn (Lattice.box w) (fire R p (fun i=>part (pullLength R i) w)):= by
    intro U V h; refine sum_congr rfl (fun i hi=> ?_); rw [scroll_glow R i w U V h,fixed_orig i U V (scroll_mon h ?_)]
    intro z hz; obtain ⟨hX,hV⟩:=box_test.mp (Finset.mem_coe.mp hz); exact box_test.mpr ⟨fun i=>by have hh:=hX i; omega,fun i=>by have hv:=hV i; omega⟩
variable {K:Type}[NormedAddCommGroup K][NormedSpace ℝ K]{U:K → Config G m}{x:Site m}{y:K}{X:Set K} (h: R.Bounds p μ C Λ) (F:ℕ→Atom G r) {E:ℝ}(hs:0<μ)(hf:SumBudget (fun i=>(F i).budget μ) E)(A:Set ℕ)
lemma reads (U:Config G m)(x:Site m): pass (stem F A) m x U=title A x F U:=rfl
lemma quadPort (Q:PlaqAxes→Set ℕ)(U:Config G m)(x:Site m) : pass (fire R p Q) m x U=∑ a:PlaqAxes,(p.direct*G.price (faceValue U (x,a))+ ‖startAt R (Q a) x a U‖^2/2):= by unfold pass fire; simp_rw [fixed_identity]; rfl
lemma bright (U:Config G m): froth (pass (fire R p (fun _=> Set.univ)) m) U= quadratic p R U:= by
   have he i a: startAt R Set.univ i a U= R.ell U (i,a):= (tsum_subtype_eq_of_support_subset (s:=Set.univ) (f:=fun j=>R.ellTerms (i,a) j U) (Set.subset_univ _)) -- syntax
   unfold froth; simp_rw [quadPort,he]; rw [quadratic,Fintype.sum_prod_type]
lemma starview (U:Config G m) : froth (pass (stem F Set.univ) m) U=uncut F U:= by unfold froth Precision.uncut; apply sum_congr rfl; intro i _; exact tsum_subtype_eq_of_support_subset (s:=Set.univ) (f:=fun j=> (F j).unmasked U i) (Set.subset_univ _)
variable {R F A}
-- bills
variable (w)
variable (hO:IsOpen X)(hc:IsPreconnected X)(hx: y∈ X) (ht:∀ i z, z∈X→Allows k (fun y=> G.mat (U y i)) z Z)
include hO hc hx ht
lemma highPair (V:PlaqAxes→Set ℕ)(y':Site m)(h:R.Bounds p μ C Λ) : Allows k (pass (fire R p V) m y' ∘ U) y ( (Fintype.card PlaqAxes:ℝ)*(|p.direct| * priceCost G (travelCost G k 4 Z) + (1/2)*(2^k:ℝ)* (C*portSize G μ Z k)^2)):= by
   have hE b:= yaw (V b) y' h hO hc hx ht b 0 (fun _ _=> Nat.zero_le _); simp only [Model.pole, Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at hE
   have ht' (a:PlaqAxes): Allows k (fun z=>G.price (faceValue (U z) (y',a))) y (priceCost G (travelCost G k 4 Z)):= (travel_jets (U:=U) (fun i=> ht i y hx) y' (show List.length (square a.val.1 a.val.2) ≤ 4 from le_rfl)).price -- edit
   unfold Function.comp; simp_rw [quadPort]; rw [← show (∑ _a:PlaqAxes,(|p.direct| * priceCost G (travelCost G k 4 Z) + (1/2)*(2^k:ℝ)* (C*portSize G μ Z k)^2))= (Fintype.card PlaqAxes:ℝ) *(|p.direct| * priceCost G (travelCost G k 4 Z) + (1/2)*(2^k:ℝ)* (C*portSize G μ Z k)^2) from (by rw [Finset.sum_const,card_univ,nsmul_eq_mul])]
   apply allows_sum (f:=fun a z=> (p.direct*G.price (faceValue (U z) (y',a))+ ‖startAt R (V a) y' a (U z)‖^2/2))
   intro i _; apply (ht' i|>.smul p.direct).add; let b z:=startAt R (V i) y' i (U z)
   have hr:= (Allows.bilinear (innerSL ℝ) (hE i) (hE i) (norm_innerSL_le _)).smul (1/2:ℝ)
   apply Allows.germ (hr.mono ?_) (Eventually.of_forall (fun x=>?_)); · rw [abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]; apply le_of_eq; ring
   change 1/2*inner ℝ (b x) (b x)=‖b x‖^2/2; rw [real_inner_self_eq_norm_sq]; ring
lemma fault_booth (h:R.Bounds p μ C Λ) (i:Site m): let V:= fun i=>part (pullLength R i) w; let Z₁ R' z:= pass (fire R p R') m i (U z); Allows k (Z₁ (fun _=> Set.univ)-Z₁ V) y ( (Fintype.card PlaqAxes:ℝ)* (pole μ w*(2^k:ℝ)*(2*(C*portSize G μ Z k)^2))) := by
   intro V u; let v (X:PlaqAxes→Set ℕ)(a:PlaqAxes) z:=startAt R (X a) i a (U z)
   let Q:= V; let V':= (fun i=>(V i)ᶜ); let T:= v Q; let W:= v V'; let A:=v (fun _=> Set.univ); have he a z:A a z=T a z+W a z:= by
     suffices hp: A a z=R.ell (U z) (i,a) by rw [hp]; have hr:= R.ell_dominated h (i,a)|>.summable (U z); exact (Summable.tsum_add_tsum_compl (s:=Q a) (hr.subtype (·∈Q a)) (hr.subtype _)).symm
     exact (tsum_subtype_eq_of_support_subset (s:=Set.univ) (f:=fun j=>R.ellTerms (i,a) j (U z)) (Set.subset_univ _))
   let P:= C*portSize G μ Z k; have hx F a: Allows k (v F a) y P:= by simpa only [Model.pole, Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using! yaw (F a) i h hO hc hx ht a 0 (fun _ _=> Nat.zero_le _)
   let B' a z:= (1/2)*inner ℝ (W a z) ((A a+T a) z)
   have hu: u (fun i=>Set.univ) - u V=(fun z=> ∑ a:PlaqAxes,B' a z):= by -- edit
       funext z; dsimp only [u, Pi.sub_apply]; simp_rw [quadPort,← Finset.sum_sub_distrib]; apply sum_congr rfl; intro a _
       change _+‖A a z‖^2/2-(_+‖T a z‖^2/2)= 1/2*inner ℝ _ ((A a+T a) z); simp only [←real_inner_self_eq_norm_sq,Pi.add_apply,he,inner_add_right,inner_add_left]; rw [real_inner_comm (W a z)]; ring
   rw [hu]; apply Allows.mono (f:=fun z=>∑ a:PlaqAxes,B' a z) (C:=(∑ _a:PlaqAxes,pole μ w*2^k*(2*P^2))) (allows_sum _); swap
   · intro a _; have hC:= yaw (V' a) i h hO hc (by assumption) ht a w (fun i hi=> (le_of_lt (lt_of_not_ge hi)))
     refine (((Allows.bilinear (innerSL ℝ) hC ((hx (fun _=>Set.univ) a).add (hx V a)) (norm_innerSL_le _))).smul (1/2:ℝ)).mono ?_
     rw [abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]; have hv:0 ≤ pole μ w*2^k*P^2:= by unfold pole; positivity
     unfold P at *; linarith only [hv]
   simp only [sum_const,nsmul_eq_mul,card_univ]; exact le_rfl
end YM.Contacts.Model
