import YM.LocalTaylorR2.Marker.Taft
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rising
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
variable {b B ρ q:ℝ}{a d a' : H.ThinP→Orders l→ℝ}{σ σ':H.ThinP→ℝ}
-- avoid naming clashes sigma universal
structure Mind (H: Cash W x μ L Q o C T R) (M : Leaf R) (χ:Chi) (l:ℕ)(v:ℝ)(j:ℕ)(ξ u:H.ThinP→Orders l→ℝ)(Z:H.ThinP→ℝ) (ρ D:ℝ):Prop where
    thought : ReadyAll (l:=l) χ (sprig H χ) v j ξ Z ρ
    credit p q: Items H p (dial M H χ (l:=l) p q) ∧ 0≤ u p q ∧ ∀ V, Healthy (Pressure.temp x) (H.smallAt p) V→ Ore V (dial M H χ p q) v (D*u p q) j
    troop p:(∑ q,u p q*ρ^q.val)≤ Z p
    good : 0≤D
variable {k₁ :ℝ} (h:Mind H M χ l v₀ j a a' σ ρ k₁) (z:H.fragrances) (take:H.fragrances→ℕ→Prop)
-- tensor with exactly one outgoing leg; others include charged Taylor errors.
abbrev tangle {α:Type*} (f g: H.ThinP→ α) (i y :Option (Fin z.fst)) := if y=i then g (z.2 y) else f (z.2 y)
def bud (χ:Chi)(l:ℕ) := tangle H z (sprig (l:=l) H χ) (dial (l:=l) M H χ)
def subtensor (χ:Chi)(l:ℕ)(V:Config G c):ℝ:=
    coefficient H.seam z.snd /↑(z.1+1).factorial * ∑ i, Products.filtered (bud M H z χ l i) (fun q=> take z (atGrade q)) V
open LeafReady

lemma recovery (V:Config G c)(χ: Chi)(l:ℕ): matin M H z χ V=subtensor M H z (fun z r=>¬take z r) χ l V+subtensor M H z take χ l V:=by
  unfold matin subtensor; rw [← mul_add,← sum_add_distrib]; apply congr_arg; apply sum_congr rfl
  intro i hi
  have hg(y): tangle H z (fun p=>leaflet H χ V p) (libs M H χ V) i y=∑ k: Orders l,bud M H z χ l i y k V:= by
    unfold tangle bud; by_cases h:y=i
    · simpa only [tangle,if_pos h] using! recovers M H (z.2 y) χ l V
    simpa only [tangle,if_neg h] using! equality H χ (z.2 y) V l
  rw [← Products.apart, ← Products.literal (f:=fun y _=> tangle H z (fun p=> leaflet H χ V p) (libs M H χ V) i y)]; swap; · exact hg
  rw [mul_comm (Finset.prod ..)]
  conv_rhs=> rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
  unfold tangle; rw [if_pos rfl]; exact congr_arg _ (prod_congr rfl (fun _ h=> (if_neg (ne_of_mem_erase h)).symm))
lemma censored (χ : Chi)(l:ℕ)(he:¬speaks M H z): subtensor M H z take χ l=0:=by
    funext V; unfold subtensor; rw [Finset.sum_eq_zero,mul_zero]; rfl
    intro i hi; apply Finset.sum_eq_zero; intro q hq; unfold Products.atGrades bud; apply Finset.prod_eq_zero (mem_univ i); unfold tangle; rw [if_pos rfl,Marker.lull M H (z.2 i) (show ¬ treads M H (z.2 i) from fun h=> he ⟨i,h.2,h.1.2⟩)]
include h
open Gas in
lemma budget (i:H.ThinP) : 0 ≤ σ i := by
    refine le_trans (b:=∑ q, a i q *ρ^q.val) ?_ (h.thought.bounds i)
    exact sum_nonneg (fun j _=> mul_nonneg (h.thought.pos ..) (pow_nonneg (by have he:=h.thought.scale; positivity) _))

set_option maxHeartbeats 600000 in
lemma tensor (p : ℕ)(hp:∀ q,take z q→ p ≤ q): let Z:= reachability z; let F := subtensor M H z take χ l
    let u:= clusters H.seam (fun i=>2*(2^j*σ i)) z.snd
    GaugeInvariant F ∧ Measurable F ∧ LocalOn Z F ∧
      ∀ U, Healthy (Pressure.temp x) Z U → Ore U F v₀ (k₁*(ρ^p)⁻¹*u) j:=by
   intro Z F u
   let c:ℝ:=coefficient H.seam z.snd/↑(z.1+1).factorial
   let st i:= Products.filtered (bud M H z χ l i) (fun q=>take z (atGrade q))
   have ht i y t: Items H (z.2 y) (bud M H z χ l i y t):=by
      unfold bud tangle; split
      · exact (h.credit ..).1
      exact h.thought.letter ..
   refine ⟨fun i y=> ?_, measurable_const.mul (Finset.measurable_fun_sum _ (fun i _=> Finset.measurable_fun_sum _ fun q _=> Finset.measurable_fun_prod _ fun t _=> (ht i t (q t)).2.1)), fun V U h=> ?_, fun V hV E _ _ _ U y hx he=>?_⟩
   · unfold F subtensor; apply congr_arg
     exact sum_congr rfl fun j _=>sum_congr rfl fun m _=> prod_congr rfl fun k _=> (ht j k (m k)).1 i y
   · unfold F subtensor; exact congr_arg _ (sum_congr rfl (fun i _=> sum_congr rfl (fun q _=> prod_congr rfl (fun t _=> (ht i t (q t)).2.2 _ _ (agrees_mono h (coe_subset.mpr (subset_biUnion_of_mem (H.smallAt ∘ z.snd) (mem_univ t))))))))
   have hm:=h.good; have hr':=h.thought.scale
   let f i t := st i (U t)
   have hv (k): Healthy (Pressure.temp x) (H.smallAt (z.2 k)) V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.snd) (mem_univ k)) hV
   let e:= ∏ i,2^j*σ (z.2 i); let q':= (ρ^p)⁻¹
   have hf (i): Brush j (k₁*q'*e) 1 (f i) y := by
      let f' t q s:= bud M H z χ l i t q (U s)
      let g r q:= k₁*a' r q
      let v:= tangle H z a g i; let w:=tangle H z σ (fun i=>k₁*σ i) i
      have hJ(k:Option (Fin z.fst))(v':Orders l): Brush j (v k v') 1 (f' k v') y:= by
         unfold v f' bud tangle; split_ifs
         · exact (h.credit ..).2.2 _ (hv k) E U y hx he
         exact h.thought.budget _ _ V (hv k) E U y hx he
      have hf k:(∑ q: Orders l,v k q*ρ^q.val) ≤ w k:=by
         unfold v w tangle; by_cases hK:k=i
         · simp_rw [if_pos hK,g,mul_assoc,← mul_sum]; exact mul_le_mul_of_nonneg_left (h.troop _) hm
         simp_rw [if_neg hK]; exact h.thought.bounds _
      have hS:= Products.retains f' v w ρ (fun _ (x:Orders l)=> x.val) (fun q=> take z (atGrade q)) hJ p (fun _ he=>hp _ he) hr' hf
      have he: ∏ i:Option (Fin z.fst), (2^j*w i)=k₁*e:=by
         unfold e; rw [← Finset.mul_prod_erase _ (fun i=> 2^j*w i) (mem_univ i),← Finset.mul_prod_erase _ (fun k=>2^j*σ (z.2 k)) (mem_univ i)]
         rw [show w i=k₁*σ _ from if_pos rfl, show ∏ k∈univ.erase i, (2^j*w k)=_ from prod_congr rfl (fun k (h:k∈univ.erase i)=> congr_arg (fun v:ℝ=> 2^j*v) (show w k=σ (z.2 k) from if_neg (ne_of_mem_erase h)))]; ring
      rw [he,mul_left_comm,←mul_assoc] at hS; exact hS
   apply ((Brush.spree univ f _ zero_le_one (fun i _=> hf i)).smul c).climb _ le_rfl
   rw [sum_const,nsmul_eq_mul, card_univ,Fintype.card_option]
   set d:= Fintype.card (Fin z.fst)+1 with hd
   have ht: (d:ℝ) ≤ (2:ℝ)^d:= by exact_mod_cast (Nat.lt_two_pow_self (n:=d)).le
   have hL :0≤e:=Finset.prod_nonneg fun i _=> mul_nonneg (by positivity : 0≤(2:ℝ)^j) (budget M H h _)
   have hQ :0≤k₁*q'*e:= mul_nonneg (mul_nonneg hm (by unfold q'; positivity)) hL
   apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht hQ) (norm_nonneg c)); apply le_of_eq
   unfold u clusters c; rw [Real.norm_eq_abs, abs_div,abs_of_nonneg (by positivity : (0:ℝ)≤ ((z.1+1).factorial:ℝ)), Finset.prod_mul_distrib, Finset.prod_const,card_univ,Fintype.card_option]; unfold d q' e; ring
end YM.LocalTaylorR2.Marker
