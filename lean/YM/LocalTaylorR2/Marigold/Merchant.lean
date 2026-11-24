import YM.LocalTaylorR2.Marigold.Wire
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
variable {k₁ :ℝ} (h:Mind H M χ l v₀ j a a' σ ρ k₁) (z:H.fragrances) (take:H.fragrances→ℕ→Prop)
variable (ψ:Copper.Stems T)
abbrev sennet(χ:Chi)(l:ℕ) := tangle H z (mintC H χ ψ (l:=l)) (fun p=>dream M H p χ ψ (l:=l)) -- syntax
def routeP (χ:Chi)(l:ℕ)(V:Config G c):ℝ:=
    coefficient H.seam z.snd /↑(z.1+1).factorial * ∑ i, Products.filtered (sennet M H z ψ χ l i) (fun q=> take z (atGrade q)) V
open LeafReady

lemma gooff (χ : Chi)(l:ℕ)(he:¬speaks M H z): routeP M H z take ψ χ l=0:=by
    funext V; unfold routeP; rw [Finset.sum_eq_zero,mul_zero]; rfl
    intro i hi; apply Finset.sum_eq_zero; intro q hq; unfold Products.atGrades sennet; apply Finset.prod_eq_zero (mem_univ i); unfold tangle; rw [if_pos rfl]; exact if_neg (show ¬ lush M H (z.2 i) from fun h=> he ⟨i,h.1.2,h.1.1.2⟩)
variable {r₁ d₀ C₀ v₁:ℝ} {ξ:Utopia H j v₁ d₀ r₁ C₀ χ} (hS:Copper.Solfege H ξ ψ)
structure Attire (H:Cash W x μ L Q o C T R)(M:Leaf R)(ψ:Copper.Stems T)(l:ℕ)(χ:Chi)(j:ℕ) (a a':H.ThinP→Orders l→ℝ)(k₁ v₀:ℝ) : Prop where
   mark : ∀ i f, ∀ V, Healthy (Pressure.temp x) (H.smallAt i) V→ Ore V (dream M H i χ ψ f) v₀ (k₁*a' i f) j
   shoulder : ∀ i f, ∀ V, Healthy (Pressure.temp x) (H.smallAt i) V → Ore V (mintC H χ ψ i f) v₀ (a i f) j
variable (h' : Attire H M ψ l χ j a a' k₁ v₀)
include hS h h'
set_option maxHeartbeats 600000 in
lemma voyager (p : ℕ)(hp:∀ q,take z q→ p ≤ q): let Z:= reachability z; let F := routeP M H z take ψ χ l
    let u:= clusters H.seam (fun i=>2*(2^j*σ i)) z.snd
    GaugeInvariant F ∧ Measurable F ∧ LocalOn Z F ∧
      ∀ U, Healthy (Pressure.temp x) Z U → Ore U F v₀ (k₁*(ρ^p)⁻¹*u) j:=by
   intro Z F u
   let c:ℝ:=coefficient H.seam z.snd/↑(z.1+1).factorial
   let st i:= Products.filtered (sennet M H z ψ χ l i) (fun q=>take z (atGrade q))
   have ht i y t: Items H (z.2 y) (sennet M H z ψ χ l i y t):=by
      unfold sennet tangle; split
      · exact supine M H _ hS _
      exact mercurial H _ hS _
   refine ⟨fun i y=> ?_, measurable_const.mul (Finset.measurable_fun_sum _ (fun i _=> Finset.measurable_fun_sum _ fun q _=> Finset.measurable_fun_prod _ fun t _=> (ht i t (q t)).2.1)), fun V U h=> ?_, fun V hV E _ _ _ U y hx he=>?_⟩
   · unfold F routeP; apply congr_arg
     exact sum_congr rfl fun j _=>sum_congr rfl fun m _=> prod_congr rfl fun k _=> (ht j k (m k)).1 i y
   · unfold F routeP; exact congr_arg _ (sum_congr rfl (fun i _=> sum_congr rfl (fun q _=> prod_congr rfl (fun t _=> (ht i t (q t)).2.2 _ _ (agrees_mono h (coe_subset.mpr (subset_biUnion_of_mem (H.smallAt ∘ z.snd) (mem_univ t))))))))
   have hm:=h.good; have hr':=h.thought.scale
   let f i t := st i (U t)
   have hv (k): Healthy (Pressure.temp x) (H.smallAt (z.2 k)) V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.snd) (mem_univ k)) hV
   let e:= ∏ i,2^j*σ (z.2 i); let q':= (ρ^p)⁻¹
   have hf (i): Brush j (k₁*q'*e) 1 (f i) y := by
      let f' t q s:= sennet M H z ψ χ l i t q (U s)
      let g r q:= k₁*a' r q
      let v:= tangle H z a g i; let w:=tangle H z σ (fun i=>k₁*σ i) i
      have hJ(k:Option (Fin z.fst))(v':Orders l): Brush j (v k v') 1 (f' k v') y:= by
         unfold v f' sennet tangle; split_ifs
         · exact h'.mark _ _  _ (hv k) E U y hx he
         exact h'.shoulder _ _ V (hv k) E U y hx he
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
variable {A : BudgetPoint} {u₀ η:ℝ} (hb:A.B=radiusB x) (hv:A.threshold=Pressure.temp x)(hr:A.order≤j) (hq:0≤q)(ht:Sailor G A.threshold q j) (hm:j*q≤ v₀) (hp:0<v₀)
    (hδ:0<η)(he:Ready H.smallAt (radiusB x) (fun i=>2*(2^j*σ i)) (u₀+η) w η (1/2))
open LeafReady

set_option quotPrecheck false
local notation "zK"=> (clusters H.seam (fun i=> 2*(2^j*σ i)) z.2)
-- uniform regulator price; explicit collar.Note no Candidate.K.
include hv hr hq ht hm hp
lemma cones (o':Site c)(hy:o'∈ M.crest.image S.ratio.parent)(r:ℕ)(hs:∀ q,take z q→ r≤q): let f := routeP M H z take ψ χ l; let Z:= locus M H o' z; let u:= brushPrice M H z j σ r A.power k₁ ρ o'
    A.Regular Z f ∧ A.supBounds o' Z f u:=by
    intro f Z u; unfold Z u brushPrice; by_cases hx:speaks M H z
    swap; · unfold f; rw [gooff M H z take ψ χ l hx,if_neg hx]; exact ⟨AnalyticBridge.VerifiedReset.reg_const (p:=A) 0,by simpa only [abs_zero] using! (AnalyticBridge.VerifiedReset.sup_const (p:=A) (G:=G) (X:=Z) (o:=o') 0)⟩
    have hy':= seatY M H o' hy z
    unfold locus at hy' ⊢; rw [if_pos hx] at hy'; simp_rw [if_pos hx]; let Z:= H.bookFoot (.inr z)
    have hw:=h.thought.scale; have hΔ:=h.good; have hσ i : 0≤2*(2^j*σ i):=by have hh:=budget M H h i; positivity
    have hb:= mul_nonneg (mul_nonneg hΔ (by positivity : 0≤(ρ^r)⁻¹)) (clusters_nonneg H.seam hσ z.snd)
    obtain ⟨hi,hM,hL,hP⟩:= voyager (hS:=hS) M H h z take ψ h' r hs
    have ha V (hl: Healthy A.threshold Z V) : Ore V f v₀ (k₁*(ρ^r)⁻¹*zK) j:= hP V (hv ▸ hl)
    have hh V (ht : Healthy A.threshold Z V) : ContDiffAt ℝ (↑A.order) (f ∘ increment V) 0 := (charted (ha V ht) hp).of_le (Nat.cast_le.mpr hr)
    let z':ℝ:= coverNumber (radiusB x) Z; let t:ℝ:=shiftG x*(1+z')
    have hu':0≤z':=Nat.cast_nonneg _
    have hpos:1≤t:=one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) (le_add_of_nonneg_right hu')
    refine ⟨⟨hL,hM,?_ ,hh,fun V h A l hl=> Next.Foundations.left_has A hl (hh V h)⟩,mul_nonneg (pow_nonneg (zero_le_one.trans hpos) (A.power*j)) hb,fun V hv l hl h=>?_⟩
    · assumption
    apply costsD hL ht hq o' _ hm (ha _ hv) (Y:=t) ?_ hpos l (hl.trans hr) h
    intro i he; have hf : (separation i o':ℝ) ≤ z'*(4*(radiusB x:ℝ)+2)+2*(radiusB x:ℝ) := by unfold z'; exact_mod_cast Lattice.Corona.extent Z (radiusB x) he hy'
    unfold t shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
end YM.LocalTaylorR2.Marker
