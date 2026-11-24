import YM.RGLocalTaylor.Retain.Gates
/-!
# Mark cost motion on entry at inherited E aperture
No patch predictor in marked K. Potential compatibility with such applications
requires separate service. Here keep every service *on actual Leaf & support*,
even those using the real E-vacant bits with respect to requested kernel.V
 (as at lookup Catalogue level): all tags at fixed `Awning` and `Threads`.
Physical normalization not varied. Use for *advanced* proclamation with STRICT
 Mark hats costs. Card proofs adapted from `Tinder`, `Revenue` and `Laminate`.
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


open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Trees
open PhysicalNext.Repeat.Daisy.Charity.RG12
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Merge
namespace Retain
open Match RG01.Survive Post Read Extra.Multi
open Mayer goodK Mill Fort Gala
open YM.MergeProof Accent Menu
open Lotus GridApprox.Nil Mallow
open Marker
namespace Hero
variable {τ ι : Type} [DecidableEq τ] [Fintype τ] [Fintype ι] {Cen : Marker.Census τ}
variable (Z : τ→Site f)(v:τ→ℝ)(hh:∀ i,0<v i)(M':ι→Hat Cen R)
    (u a b:ℝ) (hθ:0≤a)(hu:0≤u)
set_option quotPrecheck false
local notation "Θ_" => (fun i=>(M' i).M)
local notation "g'" => (fun i=> Menu.sumFee (M' i) v)
-- COPY of each Hat is in this weighted request. CARE progress existential.Holds.Payment.Charge 0 (per Pull policy cannot infer support of 
-- grass independently in reconstructed density). -/ -- stray prose edit
include hh hθ hu
lemma sprinkle (hp:Daisy.foam Q L)(ht:R.p.B≤ 2*radiusB s)(he:4 ≤ Q.relative)(hy:100≤ R.p.supportExponent)
   (ho : Menu.Offer Z M' v R.p.B (R.p.supportExponent-4) u)(hx:Extra.Multi.Occupancy (S.ratio.parent ∘ Z) k) (h: Palette.shipPrice L Q s k (a*u)): Palette.Plot Θ_ H (fun i=> a * Menu.sumFee (M' i) v):= by
    let W := Θ_; let g i:=g' i; let P i:=(M' i).s.val; let q i := a*g i
    have hz i t (hv:t∈P i): Z t ∈ (W i).crest := ho.sites i (mem_image_of_mem Z hv)
    refine Palette.deck W H q (fun i=>mul_nonneg hθ (Menu.timed _ hh)) Z P hx (fun i _=>?_) he hy hp ht (mul_nonneg hθ hu) ?_ h
    · obtain ⟨v,hv⟩:= (M' i).shiny; exact ⟨v,hv,hz i v hv⟩
    have hc :=fun i=> Push.AbsoluteSums.budget_scale hθ (ho.budget (Z i))
    intro t
    refine Extra.Multi.Budget.mono (hc t) (fun i=>?_) (fun i=>?_) le_rfl
    · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg hθ (Menu.timed _ hh)) (W _).profit);rfl
    split
    next hp=> dsimp only; rw [if_pos (show Z t ∈ _ from hz i t hp)]; unfold Palette.wages Menu.fare q; unfold W g; apply le_of_eq; ring
    exact (hc t).1 i
omit hh hθ hu
lemma sprinkles (Q: YM.ConnectedActivityE6.Target G P)(L:Side)(i:ℕ) : ∀ᶠ x in atTop, Palette.shipPrice L Q x i (Gala.mantle_rim G L x * (Mallow.station (betaF G x L))):=by
   let a:=(-(3/4):ℝ); let f x:=Gala.mantle_rim G L x * Mallow.station (betaF G x L)
   let k x:=((i:ℝ)*Extra.Multi.siteFactor (radiusB x)); let C:= Footprint.preCost (Q.halo+5); let E:= Real.exp ((Q.relative+1)*C); let D:= Real.exp (Q.relative*C)
   have hv : Rate G L a f:= by simpa only [show a = (1/4:ℝ) + -(1:ℝ) by unfold a; ring] using! ((Rate.power (G:=G) (L:=L) (a:=(1/4:ℝ))).mul (Rate.power (a:=-(1:ℝ))))
   have hh : Rate G L a (fun i=>k i*(E*f i)/D):= by
      simp_rw [div_eq_mul_inv]; simpa only [zero_add] using! (((((warmLane (G:=G) L Rate.radius_price).mul_left (i:ℝ)).mul (hv.mul_left E)).mul_right D⁻¹))
   filter_upwards [hh Q.rate (by unfold a; linarith [Q.start])] with x hx; exact (div_le_iff₀ (Real.exp_pos (_:ℝ))).mp ((le_abs_self (k x*(E*f x)/D)).trans hx)

def decal (G:Gauge):Decal G:= ⟨(fun _ Q _ L _ _ _ _ i x=> Palette.shipPrice L Q x (i+1) (Gala.mantle_rim G L x * (Mallow.station (betaF G x L)))), fun _ Q _=> ⟨0,fun L _ _ _ _ _ i _ _ _=> sprinkles Q L (i+1)⟩⟩

section roles
-- reconstruct EVERY Aura, even zero due to coincidence. Do not infer call at cost from all.True.V
variable (H)
variable {f':Head S→ℝ} {M: ℕ} {θ δ γ e Y uJ vJ turns w rP ξ:ℝ} (M':ι→Lotus.Leaf R) (rA:ι→ℝ) {Θ Θ' : Stencils T M}
    {σ : τ→Site c} {vP:ℝ}{N: Captain H j C' d vP Y A B r rP q n χ} -- A B overwritten earlier bind?remove this reconstruction unused anyway. Θ' quotes syntax conflict remove fonts
local notation "W'" => Laminate.VoucherL M' S M
open Laminate Palette
abbrev slate (Y:Stencils T M)(p:H.ThinP)(w:Laminate.VoucherL M' S M) : Config G c→ℝ:= packPrice rA w.1.val • (Mill.Tall H (Palette.team M' w.1) p.val Y (χ:=χ) w.2)
def forecast (σ:ℝ)(g:ι→ℝ)(j:ι):ℝ:=σ*g j
abbrev measureZ (k : W') :ℕ:= k.1.val.card
abbrev measureW (k: W') :ℕ:= k.2.val
variable (κ ρ α:ℝ)
local notation "gA" => (fun i p => (ρ^(p:W').snd.val)⁻¹*(packPrice rA p.1.val*Mill.Vbill H (Palette.team M' p.1) (i:H.ThinP).val f' j l e uJ α (creditStencil M θ ρ)))
local notation "hA" => Mill.final_bill (H:=H) (fun i=>promo M' (forecast κ rA) i f' e uJ α (creditStencil M θ ρ) H j l) M -- hA!
variable (hy:∀ i, 0≤rA i)(hv:1≤κ)
    (ht:Awning H N.conduit A B δ e uJ vJ k l) (hz:Priced N.conduit M f' θ ρ α A Θ) (hy': Quoted N.conduit M f' θ ρ α A γ Θ Θ') (ha:vJ≤α)
include ht hz hy hv ha
omit ht hz hv ha [Fintype ι] in
lemma pack (i:Finset ι):0 ≤ packPrice rA i:= prod_nonneg fun i _=> hy i
omit ht hz hv ha hy [Fintype ι] in
lemma small_pack (i:Finset ι) : packPrice (forecast κ rA) i=κ^i.card*packPrice rA i:= by unfold packPrice forecast; rw [prod_mul_distrib,prod_const]
lemma issueAck : Verse H (measureW M') (measureZ M') (slate H M' rA Θ (χ:=χ)) ρ κ vP j gA hA:=by
   have hr:=hz.scale; have hp i:= pack rA hy i; let CF (i:H.ThinP)(k: Tickets (Palette.sign M' S)):=Mill.Vbill H (Palette.team M' k) i.val f' j l e uJ α (creditStencil M θ ρ); let B i (p:Tickets (Palette.sign M' S)):=packPrice (forecast κ rA) p.val*CF i p
   refine ⟨hr,hv,fun i j=>mul_nonneg (by positivity) (mul_nonneg (pack rA hy j.fst.val) (invoice_base H _ _ ht hz)),fun i=> ?_,fun i p=>?_,fun i t U hp=>?_⟩
   · have ht(t : W'):2*gA i t * (ρ^t.2.val * κ^ t.1.val.card)=2*B i t.1:=by unfold B; rw [small_pack _ _ t.1.val]; unfold CF; dsimp only; field_simp
     change ∑ u:W', 2*gA i u*(ρ^(u.2.val)*κ^u.1.val.card)≤ (M+2:ℝ)*2* promo M' (forecast κ rA) _ _ _ _ _ _ _ _ _
     simp_rw [ht]; rw [Fintype.sum_prod_type]; simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,← mul_sum]; rw [Nat.cast_add,Nat.cast_two,promo]; unfold B CF; exact le_of_eq (mul_assoc ..).symm -- edit
   · obtain ⟨hh,h,hQ⟩:= bounded H (Palette.team M' p.1) i.val p.2 hz; exact ⟨fun u q=> congr_arg (packPrice rA p.1.val*·) (hh u q), measurable_const.mul h,fun V U hv=> congr_arg (packPrice rA p.1.val*·) (hQ V U hv)⟩
   intro E _ _ _ V x hx hV; have hh := (Mill.applause H (Palette.team M' t.1) i.val t.2 ht hz i.2.2 hp ha E V x hx hV).smul (packPrice rA t.1.val) -- `_` infer Team from t must explicit
   rw [Real.norm_of_nonneg (pack rA hy t.1.val)] at hh
   convert! hh using 1; ring

omit hz
include hy'
lemma pallet : Cooperates H (measureW M') (measureZ M') (slate H M' rA Θ (χ:=χ)) (slate H M' rA Θ' (χ:=χ)) ρ κ vP j gA hA γ := by
   have hf:= issueAck H M' rA κ ρ α hy hv ht hy'.gradeP ha; have hg:= issueAck H M' rA κ ρ α hy hv ht hy'.gradeF ha; refine ⟨hf,hg,hy'.defect,fun i p U hu E _ _ _ V x hx hV=>?_⟩
   have ht' := (Mill.responsive H (Palette.team M' p.1) i.val p.2 ht hy' i.2.2 hu ha E V x hx hV).smul (packPrice rA p.1.val)
   rw [Real.norm_of_nonneg (pack rA hy p.1.val)] at ht'; unfold slate; rw [← smul_sub]; convert! ht' using 1; ring
end roles
end Hero
end Retain
end YM.RGLocalTaylor
