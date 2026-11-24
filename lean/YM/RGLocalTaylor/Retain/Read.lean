import YM.RGLocalTaylor.Retain.Vapor
/-!
# Unmarked Reader Spirals in full cost currency
Compute the actual residual exactly as `modeled` change after
purchasing both core and partner estimates. Keep relative prop to
FULL kernel cap with no repricing when translating origin to other
appointed posts in allocation. Goals Q forest.Local.Support estimates
separate Principal.Aim. Proofs adapted from `Read.Register`.
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


open Blaze.March
namespace Retain
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open RG01.Survive Mayer goodK Trees Merge Palette Fort Laminate Mill
open Match Song Push AnalyticBridge VerifiedReset Collection Extra.Iteration Refrain Geo Quotes
open Captain Ursell Gas

namespace Gorge
variable {M m n:ℕ} {γ α β δ e vJ uJ d' w Y ρ θ:ℝ}
   {N : Captain H j C' d v Y A b r B q n χ} {f': Head S→ℝ} {Θ Θ': Stencils T M}

abbrev cover (H : Cash W s μ L Q o C T R)(Θ:Stencils T M) : Expansions H M:= fun p=> Mill.Total H p.val Θ (χ:=χ)

variable (p:BudgetPoint)(hp:p.threshold=Pressure.temp s)(hj:p.order≤j)(hk:p.power≤k)(hB:p.B=radiusB s)
    (hq:0≤q)(hS:Sailor G p.threshold q j)(hr:j*q≤v)(hm:0<v)
    (hA:Awning H N.conduit A b d' e uJ vJ l m) -- reversed k l occupancy vs block?
    (hh:Priced N.conduit M f' θ ρ α A Θ)(he:vJ≤α)
    (hK: Quoted N.conduit M f' θ ρ α A γ Θ Θ')
local notation "a'" => cover H (χ:=χ)
local notation "A'" => cover H Θ (χ:=χ)
local notation "t'" => cover H Θ' (χ:=χ)
local notation "g₀" => (fun i=> billBase H i f' j m e uJ α (creditStencil M θ ρ))
local notation "g'" => Mill.final_bill g₀ M (H:=H)
set_option quotPrecheck false
local notation "F₀" => (fun i u=>(ρ^(u:Orders M).val)⁻¹ * g₀ ((i:H.ThinP).val))
include hA hh he
lemma core : Verse H (fun x:Orders M=>x.val) (fun _=>0) (cover H Θ (χ:=χ)) ρ 1 v j F₀ g':= by
   have hx:=hh.scale; let T:=Mill.idle R; have hQ (i:H.ThinP)(t:Orders M):cover H Θ (χ:=χ) i t= Tall H T i.val Θ (χ:=χ) t:= by unfold cover; rw[metBase H]
   have ht i:0 ≤ g₀ i := invoice_base H T i hA hh
   refine ⟨hh.scale,le_rfl,fun i j=> mul_nonneg (by positivity) (ht _),fun i=> ?_,fun i t=>?_,fun i t U hu=> ?_⟩
   · let V := g₀ i.val; have hw(t:Orders M): 2*((ρ^t.val)⁻¹ * V) * (ρ^t.val*(1:ℝ)^(0:ℕ))= 2*V := by field_simp
     change ∑ t:Orders M, 2*((ρ^t.val)⁻¹*V)*(ρ^t.val*1^(0:ℕ)) ≤ _; simp_rw [hw]; rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; exact Eq.le (by push_cast; unfold Mill.final_bill V; ring)
   · rw [hQ]; exact bounded H T i.val t hh
   rw [hQ]; exact applause H T i.val t hA hh i.2.2 hu he -- order hv
omit hh
include hK
lemma cooperation : Cooperates H (fun x:Orders M=>x.val) (fun _=>0) (cover H Θ (χ:=χ)) (cover H Θ' (χ:=χ)) ρ 1 v j F₀ g' γ:=by
   refine ⟨core (hA:=hA) hK.gradeP he,core hA hK.gradeF he,hK.defect,fun i t U hu=>?_⟩
   unfold cover; rw [metBase,metBase]; exact responsive H (Mill.idle R) i.val t hA hK i.2.2 hu he

omit he hA hK in
lemma fieldEq (keep:H.fragrances→ℕ→Prop) (z:H.fragrances) (Θ:Expansions H M): Read.field keep Θ z=∑ i∈ univ.filter (fun i:lot z (Orders M)=> keep z (dots (fun i:Orders M=>i.val) z i)), Mill.printed Θ z i:= by
   ext V; unfold Read.field; rw [Finset.sum_apply, Finset.mul_sum]; rfl -- test

omit he hA hK
open RGLocalTaylor.Read
variable {J : Rep G f}{U' : Cash W s μ L Q o C T J}
    (X : Match.Alliance U' H 1 0)
    (take:H.fragrances→ℕ→Prop) {r₁:ℕ}(hT:∀ i j,take i j→ r₁≤j)

-- un-oriented Beam budget. Used after re-expression with keep K unchanged.
abbrev stencil (f':H.fragrances→ Config G c→ℝ): Magazine U' → Config G c→ℝ:= Sum.elim (fun i=> (-1:ℝ) • f' (X.furrow i)) (fun _=>0)
local notation "f₂" => Read.field take A'
local notation "f₁" => Read.field take t'
local notation "e!" => ((ρ^r₁)⁻¹*γ)
local notation "cζ" => (collars G δ s j k*(w * ((1-β)⁻¹)))

-- support hit test transfer to its translated origin. compact unary use
structure Film (p:BudgetPoint) (g:H.fragrances→ Config G c→ℝ) (e:ℝ) : Prop where
   seats : ∃ f, Ac.Hit (Captain.reachability (H:=H)) p.B f (preExponent p) e ∧ ∀ i, p.Regular (reachability i) (g i) ∧ ∀ x∈ reachability i, p.supBounds x (reachability i) (g i) (f i)
variable {ξ:H.fragrances → Config G c→ℝ}
lemma recording (hp:Film p ξ w) : orient p (Beam.marquee U' p).reg (Song.choir (stencil X ξ) ∘ Song.pennant U') (turnFee p*w):=by
   obtain ⟨f,h,hF⟩:=hp.seats; let Z:= Beam.contents U' p; let g : Magazine U'→ℝ:= Sum.elim (fun i=>f (X.furrow i)) (fun _=>0); let S := stencil X ξ
   have hX i:(Z (.inl i)).support=Song.perf H (X.furrow i):=(Beam.patch U' p _).trans (Song.reconnects U' X i)
   have hW (i): p.Regular (Z i).support (S i) ∧ p.supBounds (Z i).site (Z i).support (S i) (g i):=by
      rcases i with i|i
      · rw [hX]; exact ⟨CouplingShape.reg_scale _ (hF _).1, by simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) ((hF _).2 (Z (.inl i)).site (show (Z (.inl i)).site∈ reachability _ from (show (Z (.inl i)).site∈ perf H _ from (hX i) ▸ (Z (.inl i)).anchor)))⟩
      exact ⟨CouplingShape.reg_const _, by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (o:=(Z (.inr i)).site) (X:=(Z (.inr i)).support) 0)⟩
   have ht:Meadow.Budget p Z S w:=by
      refine ⟨g,fun i=>?_,hW⟩; rw [← add_zero w]; apply Cost.sum
      · refine budget_mono (Cost.equiv X.furrow (h i)) (fun j=> ?_) fun j=>?_
        · split; next=> exact mul_nonneg ((hW (.inl _)).2.1) (Real.exp_pos _).le
          exact le_rfl
        dsimp only; split
        next hh=>
           rw [if_pos (show i∈ reachability _ from hh ▸ (show _ ∈ perf H (X.furrow j) from (hX j) ▸ (Z (.inl j)).anchor)), show (Beam.contents U' p (Sum.inl j)).support=_ from hX j]; exact le_rfl
        exact (Cost.equiv X.furrow (h i)).1 j
      exact by simp [SumBudget,g] -- hp uses
   obtain ⟨f,h,hx⟩:= ht; obtain ⟨hc,ht⟩:= Song.spiral _ _ f (fun i=>(hx i).1) (fun i=>(hx i).2) h
   exact ⟨_,fun i=>Cost.equiv (Song.pennant U') (ht i), fun i=>hc (Song.pennant U' i)⟩

variable (hα: preExponent p ≤ a)(hδ:0<δ)
set_option quotPrecheck false
-- ready explicit use @ arg to avoid panic
include hK hT hp hk hj he hm hB hA hq hr hS hα hδ
lemma first_time (hR:Ready H.smallAt p.B (fun i=>2^j*g' i) (a+δ) w δ β): Film p (Read.field take (cover H Θ (χ:=χ)) - Read.field take (cover H Θ' (χ:=χ))) (e! * cζ) := by
   let f(i):= e! * LeafReady.allowance p i j k g'; have hh:=cooperation hA he hK
   have hg:= hK.gradeP.scale; have hζ:0≤ e!:=mul_nonneg (by positivity) hK.defect
   have h:= couponBudget p (a:=a) (k:=k) (by apply le_trans (_:0≤preExponent p) hα; unfold preExponent; have hx:=p.exponent_pos; positivity) hα hδ hζ hR
   refine ⟨f,h,fun i=> ?_⟩; let Z:=reachability i; let K:=univ.filter (fun u:lot i (Orders M)=>take i (dots (fun i:Orders M=>i.val) i u)); let U:= Laminate.Axle.radiusP (j:=j) (k:=k) p i
   let V(t):=Mill.printed A' i t-Mill.printed t' i t
   have he' : (f₂-f₁) i=∑ u∈K,V u := by rw [Pi.sub_apply,fieldEq take,fieldEq take,← sum_sub_distrib]
   have hf:= fun u=>Mill.defectC hh i p u hp hj hk hB q hq hS hr hm
   have hF : ∑ u∈K, U*Mill.salary F₀ j i u ≤(ρ^r₁)⁻¹ * LeafReady.allowance p i j k g':=by
      simpa only [PriceA,one_pow,mul_one] using! Mill.picture (k:=k) (r₁:=r₁) (r₂:=0) (w'S:=K) hh.formalP i p (fun u h=> ⟨hT i _ ((mem_filter.mp h).2),Nat.zero_le _⟩)
   rw [he']; refine ⟨Meadow.regularA _ (fun i _=>(hf i).1),fun x hx=>?_⟩
   refine VerifiedReset.sup_le (Trio.sup_S p V _ K Z x (fun i _=>(hf i).1) (fun i _=>(hf i).2 x hx)) ?_; rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left hF hK.defect).trans_eq (by rw [← mul_assoc, mul_comm γ]) -- f equality?
end Gorge
end Retain
end YM.RGLocalTaylor
