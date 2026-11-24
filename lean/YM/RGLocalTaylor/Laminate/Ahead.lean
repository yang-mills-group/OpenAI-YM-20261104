import YM.RGLocalTaylor.Laminate.Slice
import YM.MergeProof.Endow

/-!
# Incoming marker-pressure and nilpotent exponent assembly cost

Advertise a Sheet `Clearing`: ALL derivative/current/mode genuine germ
costs and pay with the actual margin. Bounds for headSheet and for
EVERY contributing main/residual certificate even before census operations and
packing onto clouds. All *final payout indicators* on these same supports and
basis decisions apply (`Accented.Burns` with Towed). Includes footprint and
price before summation. Meant to permit direct transportation & readout using
same convention there. Do not upgrade to a different Post basis or supports
for free. Adapted from `Read.Germ` & Jetting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March Captain
namespace Laminate
open RG01.Survive Trees Merge Palette Gas Ursell Marker GridApprox.Nil
open MergeProof.Accent AnalyticBridge VerifiedReset Quotes Next.Foundations
variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (N : Captain H j C' d v Y A b r B q n χ)
    {τ:Type} [DecidableEq τ] {Cen : Marker.Census τ}(o': τ→Site c) (p:BudgetPoint) (y:ι→Poly Cen) (cost:τ→ℝ) (keep:H.fragrances→ℕ→Prop) (z:H.fragrances)
variable (hy : ∀ i,(y i).part Cen.quiet=0) (hc:∀ i,0<cost i) (hs:∀ i,Poly.price cost (y i) ≤ 1)
    (hq:∀ i,GridApprox.Nil.Scoped (A:={j:τ|o' j∈(M' i).crest.image S.ratio.parent}) (y i))
-- [Fintype τ]? R.Census τ has Fin & quiet. Scoped needs?

def Reach (H : Cash W s μ L Q o C T R) (z:H.fragrances):= H.bookFoot (.inr z)

def Fixed (X:Support c) (U:Config G c→Poly Cen):Prop:=
  (∀ V, GridApprox.Nil.Scoped (A:={j:τ|o' j∈X}) (U V))∧∀ V,(U V).part Cen.quiet=0

def Margin (X:Support c) (e:ℝ) (U:Config G c→Poly Cen):Prop:= X.Nonempty ∧
    ∃ g : Sheet Cen, 0≤g ∧ wordsPrice cost g ≤ e ∧ ∀ i,p.Regular X (fun V=>(U V).part i) ∧ ∀ x∈ X,p.supBounds x X (fun V=>(U V).part i) (g i)

namespace Margin
variable {p cost}
variable {X':Support c} {U:Config G c→Poly Cen} {e:ℝ}(h: Margin p cost X' e U)
include h hc in
lemma nonneg :0≤e:= le_trans (sum_nonneg (fun i _=> mul_nonneg (Poly.worth hc _|>.le) (h.2.choose_spec.1 i))) h.2.choose_spec.2.1
include h
lemma staffed (hx:Fixed o' X' U) : Burns o' X' (masked p.threshold X' U) p.threshold :=by
   obtain ⟨s,g,hg,h,hL⟩:=h; let F:= masked p.threshold X' U
   have hx' v (χ: Cen.Mode): (F v).part χ=masked p.threshold X' (fun V=>(U V).part χ) v:=by unfold F; by_cases H:Healthy p.threshold X' v <;> simp [H]
   have ht(i:Cen.Mode):= (hL i).1
   refine {toBorne:=?_,permits:=fun V h=> not_not.mp (fun he=> h (masked_ne _ _ _ V he)),sil:=fun v=>?_}
   · refine ⟨fun u v hz h=>Marker.Poly.ext fun i=>?_,fun g u=> Marker.Poly.ext (R:=Cen) fun i=>?_,fun i=>?_,fun v i hv=>?_⟩
     · change (F u).part _=(F v).part _; rw [hx',hx']; by_cases h':Healthy p.threshold X' u <;> have hv:Healthy p.threshold X' u ↔ Healthy p.threshold X' v:= by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,h]
       · rw [masked_eq _ _ _ u h',masked_eq _ _ _ _ (hv.1 h')]; exact (ht i).sites u v hz
       rw [masked_ne _ _ _ u h',masked_ne _ _ _ _ (mt hv.2 h')]
     · have hU: Healthy p.threshold X' (Lattice.gauge g u)↔ Healthy p.threshold X' u:= by simp [Healthy]
       change (F _).part i=(F _).part i; rw [hx',hx']; by_cases h:Healthy p.threshold X' u; rw [masked_eq _ _ _ _ (hU.2 h),masked_eq _ _ _ _ h]; exact (ht i).symmetry g u
       rw [masked_ne _ _ _ _ (mt hU.1 h), masked_ne _ _ _ _ h]
     · change Measurable (fun U=> (F U).part i); simp_rw [hx']; exact masked_measurable _ _ _ (ht i).borel
     change (F _).part i=0; rw [hx']; by_cases h: Healthy p.threshold X' v; rw [masked_eq _ _ _ _ h]; exact hx.1 v i hv
     rw [masked_ne _ _ _ _ h]
   by_cases h: Healthy p.threshold X' v; rw [masked_eq _ _ _ _ h,hx.2]; rw [masked_ne _ _ _ _ h]; rfl
lemma rider : Loci cost (masked p.threshold X' U) e:=by
    obtain ⟨⟨s,hs⟩,g,hg,h,hL⟩:=h; refine ⟨g,hg,fun i j=>?_,h⟩; by_cases h:Healthy p.threshold X' i; rw [masked_eq _ _ _ _ h]; exact ((hL j).2 s hs).2 i h [] (Nat.zero_le _) (by simp); rw [masked_ne _ _ _ _ h,Poly.part_nil,norm_zero]; exact hg _
end Margin

def Swing {X:Type} (D:X→ Support c) (U:X→ Config G c→ Poly Cen) (a s:ℝ):Prop:=∃ v:X→ ℝ,(∀ i,Margin p cost (D i) (v i) (U i) ∧ Fixed o' (D i) (U i)) ∧ Ac.Hit D p.B v a s
namespace Swing
variable {X:Type}{o' cost p}{U:X→ Config G c→ Marker.Poly Cen}{D:X→Support c}(h : Swing o' p cost D U a s)
include h
lemma larger (hu: s ≤ η): Swing o' p cost D U a η:= ⟨h.choose, h.choose_spec.1, fun i=> budget_loosen (h.choose_spec.2 i) hu⟩  -- omit? infer hc unused
lemma burn (x:X) : Burns o' (D x) (masked p.threshold (D x) (U x)) p.threshold := ((h.choose_spec.1 x).1.staffed _ ((h.choose_spec.1 x).2)) -- namespace
lemma fleet (hc:∀ i,0<cost i) (ha:0≤a): Towed cost D (fun x=> masked p.threshold (D x) (U x)) p.B a s:=by
   obtain ⟨v,h,hV⟩:=h; have hv i:= (h i).1.nonneg hc
   have hu := Product.everyone_ne _ _ hv (fun i _=> (h i).1.1) hV
   exact ⟨v,hu.2.1.of_nonneg_of_le hv (fun i=> le_mul_of_one_le_right (hv i) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))), hV, fun i=> (h i).1.rider⟩
end Swing

variable (H) {M:ℕ}
include hq hy
lemma resident [Fintype τ] : Fixed o' (reachability z) (stained M' rA y z (χ:=χ) keep M):=by
  refine ⟨fun U i hi=> ?_,fun U=>bangs M' rA y hy z U keep M⟩
  unfold stained; rw [Poly.part_sum]; refine sum_eq_zero fun v _=>?_; unfold grain; rw [Poly.part_smul]; by_cases hp:columnKey M' rA z v (χ:=χ) U=0; rw [hp,Complex.ofReal_zero,zero_mul]
  have he j: (v j).fst.reach⊆ (z.2 j).val:= by
     by_contra h; apply hp; unfold columnKey; rw [prod_eq_zero (mem_univ j),mul_zero]; unfold mint rector column; rw [if_neg (Palette.label M' _|>.symm ▸ h),Pi.zero_apply,mul_zero]
  unfold paints; rw [scope_prod _ _ ?_ i hi, mul_zero]; intro j hj
  unfold frame; apply scope_prod; intro k hk
  have hyes : (M' k).crest.image S.ratio.parent ⊆ reachability z:= by -- based mark_hit
    intro u hu; have hh : areas R T Q.halo (radiusB s) (Palette.sign M' S k) ⊆ H.smallAt (z.2 j):= subset_biUnion_of_mem _ (he j ((v j).fst.reaches_of hk)); refine subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ j) (hh ?_)
    unfold Palette.sign; rw [(M' k).turn.badge_area]; exact halo_subset _ _ (Finset.image_subset_image (s₂:= RG.inspected (M' k).crest) Finset.subset_union_left hu)
  intro i hi; exact hq k i (fun h=> hi (h.trans fun i h=> hyes h))

omit hy hq
include hc hs
omit [Fintype ι] in
lemma paintsWorth (u:Flight M' z M): Poly.price cost (paints M' y z u)≤1:= (Poly.multiple hc _ _).trans (Finset.prod_le_one (fun _ _=> Poly.nonnegative hc _) (fun _i _=> (Poly.multiple hc _ _).trans (Finset.prod_le_one (fun _i _=> Poly.nonnegative hc _) (fun i _=>hs i))))

variable {H o' M' rA cost y}
variable {δ ρ w β v ζ:ℝ} {q:ℝ}
    {u:H.ThinP→VoucherL M' S M→ℝ}{g:H.ThinP→ℝ} (h:Axle M' rA M j H v χ u g ρ)
    (ht : p.threshold=Pressure.temp s) (hj : p.order≤j) (hp:p.power≤k) (hB:p.B=radiusB s)
    (hq':0≤q) (hS:Sailor G p.threshold q j) (hv : j*q≤v) (hr:0<v)
    (hJ: Trees.Ready H.smallAt p.B (fun i=>2^j*g i) (a+δ) w δ β)
    {K:ℕ} (hh:∀ i n,keep i n→K≤n)
set_option quotPrecheck false
local notation "w!" => LeafReady.allowance p z j k g
local notation "u'" => Axle.brands (j:=j) (k:=k) z p u
include h ht hj hp hB hq' hh hS hv hr
lemma panel : Margin p cost (Reach H z) ((ρ^K)⁻¹ * LeafReady.allowance p z j k g) (stained M' rA y z (χ:=χ) keep M):=by
    let F i:=u' i; let v j:= paints M' y z (j:Flight M' z M)
    let s:= univ.filter (passenger M' z keep (k:=M)); let g i j:= ‖(v i).part j‖*F i
    have he(i:Flight M' z M):0 ≤ F i:= Axle.brand_pos z h i p k
    let X:=Reach H z; let x:= Song.locate H z; have hx:x.site∈X:=x.anchor
    have hf(i:Cen.Mode): (fun U=> (stained M' rA y z (χ:=χ) keep M U).part i)=∑ j∈s,(v j).part i • (fun U=> (↑(columnKey M' rA z j (χ:=χ) U):ℂ)):= by
       ext U; unfold s stained grain; rw [Poly.part_sum]; simp_rw [Finset.sum_apply,Poly.part_smul, Pi.smul_apply,smul_eq_mul]; exact sum_congr rfl fun _ _=>mul_comm ..
    let U (q:Config G c→Poly Cen) (i:Cen.Mode) := fun V=> (q V).part i
    have hz i k (hh:k∈X): p.Regular X (U (stained M' rA y z (χ:=χ) keep M) i) ∧ p.supBounds k X (U (stained M' rA y z (χ:=χ) keep M) i) (∑ j∈s,g j i):=by
       unfold U; rw [hf]; refine Next.Foundations.regular_bound_sum _ _ _ (fun j _=>?_) ; obtain ⟨he,hZ⟩:=Axle.atSizes z k hh h j ht hj hp hB q hq' hS hv hr; exact ⟨Next.Foundations.regular_smul _ (VerifiedReset.regular_mapped Complex.ofRealCLM he), Next.Foundations.bound_smul _ ((VerifiedReset.sup_real he).2 hZ)⟩
    refine ⟨⟨x.site,hx⟩,fun i=>∑ j∈s,g j i, fun i=> sum_nonneg (fun _ _=> mul_nonneg (norm_nonneg _) (he _)),?_,fun i=> ⟨(hz i _ hx).1,fun x hh=>(hz i x hh).2⟩⟩
    unfold wordsPrice g; dsimp only; simp_rw [Finset.mul_sum]; rw [sum_comm]; refine le_trans (Finset.sum_le_sum (g:=F) (fun i _=>?_)) (Axle.rents z h keep hh); simp_rw [← mul_assoc,← Finset.sum_mul]; exact mul_le_of_le_one_left (he i) (paintsWorth (hc:=hc) (hs:=hs) _ ..) -- args

omit hc hs ht hj hp hB hq' hS hv hr hh
include hJ
variable (ha:0≤a) (hh': ζ ≤ a) (hh0:0 ≤ ζ) (hδ:0<δ)
include ha hh' hδ
private lemma hitTop : Ac.Hit (Reach H) p.B (fun z=> (ρ^K)⁻¹*LeafReady.allowance p z j k g) ζ ((ρ^K)⁻¹*(collars G δ s j k*(w*(1-β)⁻¹))):= by
  let Z:= Reach H; let c0:= (ρ^K)⁻¹; have hu:0<c0:=by unfold c0; have hf:=zero_lt_one.trans_le h.strong; positivity
  have hp:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hV := hJ.2.2.2.2.1
  intro x
  have hz:=Ursell.log_hit_tail _ _ _ H.testS hJ (add_nonneg ha hδ.le) 0 x; simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
  let v:= collars G δ s j k
  have ht:0≤v:=by unfold v collars Reserves.polyPrice; positivity
  have hh := budget_scale hu.le (budget_scale ht hz)
  refine budget_mono hh (fun z=>?_) fun z=> ?_
  · split
    next=> exact mul_nonneg (mul_nonneg hu.le (mul_nonneg (pow_nonneg (zero_le_one.trans (Axle.dmeter_pos ..)) _) (clusters_nonneg _ hV _))) (Real.exp_pos _).le
    exact le_rfl
  split
  next hy=>
    have hv: x∈ Z z:=hy
    let t:ℝ:=coverNumber p.B (Z z)
    let Hq:= clusters H.seam (fun i=>2^j*g i) z.snd
    have hu':0≤Hq := clusters_nonneg _ hV _
    have he':0≤t:=Nat.cast_nonneg _
    rw [if_pos (show x∈unionOf H.smallAt z.2 from hv)]; change c0*((shiftG s*(1+t))^(j*k)*Hq) * Real.exp (_*t) ≤ c0*(v*(Hq*Real.exp ((a+δ)*t)))
    unfold v collars; rw [Nat.mul_comm j k,mul_pow,add_mul a, Real.exp_add]
    have he := polynomial_cost hδ he' (k*j)
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (pow_nonneg hp _)) hu') hu.le) (Real.exp_pos _).le)
    unfold Reserves.polyPrice
    nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hh' he'))
      (show 0≤c0*(((shiftG s)^(k*j)*(δ⁻¹^(k*j)* ↑((k*j).factorial) * Real.exp δ*Real.exp (δ*t)))*Hq) by positivity)]
  exact hh.1 z
include hc hs ht hj hp hB hq' hh hS hv hr hy hq
lemma ahead [Fintype τ] : Swing o' p cost (Reach H) (fun z=>stained M' rA y z (χ:=χ) keep M) ζ ((ρ^K)⁻¹*(collars G δ s j k*(w*(1-β)⁻¹))):=
    ⟨_, fun i=> ⟨panel p keep i hc hs h ht hj hp hB hq' hS hv hr hh,resident (hq:=hq) (hy:=hy) _ ..⟩, hitTop p h hJ ha hh' hδ⟩
end Laminate
end YM.RGLocalTaylor
