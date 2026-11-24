import YM.RGLocalTaylor.Retain.Telescope
/-!
# Generic filtered prices in real Taylor, Distortion before integration
For substituting an inherited predictive stencil part for any subset of the
local Taylor power handles. No changing history/authorization. Keeping
not only log prescription but the actual kernel funds as-spec. Does
not move any supports. Full error INCLUDING unestimated history tails at
same Passport prices from actual thermal bill at true S. Coupling and
support exponent/arities bought at caller. Goal powerful inheritance stability
estimate for REAL History, prove these hypotheses without appealing to smooth
kernel comparison at another coupling, e.g. using hermit/Paint. Scope ledger.
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
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
namespace Retain
open Mayer
-- ONE SUCH STENCIL FOR THIS ORDER. extra dependency in `own` not used by all
-- instances; last (grade M+1) never supplied for actual estimates.
abbrev Stencils (T : Tube G S)(M : ℕ):= Finset ℕ → Fin (M+1) → Head S → Insert T
def physical (H : Cash W s μ L Q o C T R)(M :ℕ) : Stencils T M :=fun u k i=> kernelQuote H u k i
namespace goodK
-- All estimates through one order `ℓ = i.val+1`, Full mixed uses occupant.
abbrev columnPrice (θ ρ:ℝ)(w:Head S→ℝ)(i: Head S)(l:ℕ) := (ρ^l)⁻¹*(θ*ρ)*w i

variable {M : ℕ} {Ξ : Utopia H j v d r C' χ}
   {θ ρ α γ:ℝ} {w : Head S→ℝ} {u t: Stencils T M}
local notation "u₀" => columnPrice θ ρ w
structure Priced (Ξ: Utopia H j v d r C' χ)(M:ℕ)(w:Head S→ℝ)(θ ρ α A :ℝ)(st:Stencils T M) : Prop where
   -- bound excludes condition p. Enough for ANY occurrence without retiming.
   sound (Y : Finset ℕ)(p:Fin (M+1)) (hp:p.val < M)(i:Head S)(he:Exponential i) : Fits H (st Y p i) (H.supportP i) j
   cost (Y : Finset ℕ)(p:Fin (M+1)) (hp:p.val < M)(i:Head S)(he:Exponential i) : EstFactor Ξ i (st Y p i) A (columnPrice θ ρ w i (p.val+1)) α
   nonneg : ∀ i,0≤w i
   scale : 1 ≤ ρ
   effort : 1≤α
   value : 1 ≤ θ
structure Quoted (Ξ: Utopia H j v d r C' χ)(M:ℕ) (w:Head S→ℝ) (θ ρ α A γ:ℝ) (u t:Stencils T M) : Prop where
   gradeP : Priced Ξ M w θ ρ α A u
   gradeF : Priced Ξ M w θ ρ α A t
   defect : 0 ≤ γ
   bill (Y : Finset ℕ)(p:Fin (M+1)) (hp:p.val < M)(i:Head S)(he:Exponential i) : EstFactor Ξ i ((u Y p i).difference (t Y p i)) A (γ*columnPrice θ ρ w i (p.val+1)) α

variable {p z:Molecule S} (U : Decors z M) 
variable {f' : Head S→ Insert T} {g : Head S→ℝ}
def payloadT (u : Stencils T M)(p:Molecule S)(f' : Head S→ Insert T)(U : Decors z M)(i : Head S) : Insert T := if h:i∈z then u (own p) (U ⟨i,h⟩) i else f' i
abbrev parcel (u:Stencils T M) (p:Molecule S)(f' : Head S→Insert T) (U:Decors z M) := Insert.joined p (payloadT u p f' U)

def rateLeaf (g : Head S→ℝ) (w : Head S→ℝ)(θ ρ:ℝ) (U : Decors z M) (i:Head S) : ℝ:= if h:i∈z then columnPrice θ ρ w i ((U ⟨i,h⟩).val+1) else g i
set_option quotPrecheck false
local notation "a'" => rateLeaf g w θ ρ U
local notation "price₀" => (∏ i∈p,a' i)
def older (p z:Molecule S)(g w : Head S→ℝ): ℝ := (∏ i∈p\z, g i)*(∏ i∈z,w i)
local notation "u'" => (older p z g w)

lemma fair_ledger (h:z⊆p) : price₀=(ρ^(decorOrder U))⁻¹*((θ*ρ)^z.card*u') := by
   rw [← prod_sdiff h]; have hv : ∏ i∈p\z,a' i=∏ i∈p\z,g i:=prod_congr rfl fun i hi=> dif_neg (mem_sdiff.mp hi).2
   rw [hv]; have hQ : ∏ i∈ z,a' i= (ρ^decorOrder U)⁻¹*((θ*ρ)^z.card*∏ i∈z,w i):= by
      unfold decorOrder; rw [← prod_attach z,← prod_attach z w,← prod_pow_eq_pow_sum,← prod_inv_distrib, show (θ*ρ)^z.card=∏ _k:↥z, θ*ρ by simp, show attach z=univ from rfl, ← prod_mul_distrib,← prod_mul_distrib]; apply prod_congr rfl; intro i _; unfold rateLeaf columnPrice; rw [dif_pos i.property]; apply mul_assoc
   rw [hQ]; unfold older; ring

lemma bare (p:Molecule S)(hp:Start p) (X:Coat T F)(z':Air f G) : z' ∈ X.catastrophe (o.ξ/2) R.beta (blaze p):= by
   apply (crash_summed p z' _ _).2; intro i hi; rw [noBlaze (hp i hi)]; exact fun w hw => False.elim (notMem_empty w hw)
lemma chance {p:Molecule S}(hp:Start p):blaze p=∅:= by
   refine eq_empty_of_forall_notMem (fun w hw=>?_); obtain ⟨v,hv⟩:= hp (.inr (.inr (.inr w))) (Finset.mem_toRight.mp (Finset.mem_toRight.mp (Finset.mem_toRight.mp hw))); simp only [badge,Sum.inr.injEq] at hv; contradiction

variable (hu : Priced Ξ M w θ ρ α A u) (he: ∀ i∈p \ z, EstFactor Ξ i (f' i) A (g i) α)
    (hf : ∀ i∈p\z,Fits H (f' i) (H.supportP i) j) (hb : ∀ i∈p\z,0≤g i)
    (hp:Start p)(hV:z⊆p)(hy : troupe T R Q.halo (radiusB s) p) (ht:decorOrder U≤ M)
include hu
lemma effP (i: Head S) (l:ℕ) : 0 ≤ u₀ i l:= by unfold columnPrice; have h:=hu.scale; have hv:=hu.value; have hL:=hu.nonneg i; positivity
include hb
lemma ledger (i:Head S)(hi:i∈p):0≤a' i:= by unfold rateLeaf; split; exact effP hu i _; next h=> exact hb _ (mem_sdiff.mpr ⟨hi,h⟩)
omit hb
include hp ht
lemma fits_parcel (hf : ∀ i∈p\z,Fits H (f' i) (H.supportP i) j) : Fits H (parcel u p f' U) (H.unionP p) j:= by
   apply Fits.joined; intro i hi; apply Fits.bigger (u:=H.supportP i) _ (subset_biUnion_of_mem H.supportP hi)
   unfold payloadT; split; next h=> exact hu.sound _ _ (decorOrder_lt ht _) i (hp i hi)
   next h=> exact hf _ (mem_sdiff.mpr ⟨hi,h⟩)
include he
lemma postAt (i:Head S)(hi:i∈p): EstFactor Ξ i (payloadT u p f' U i) A (a' i) α:= by
   unfold payloadT rateLeaf; split; next h=> exact hu.cost _ _ (decorOrder_lt ht _) i (hp i hi)
   next h=> exact he _ (mem_sdiff.mpr ⟨hi,h⟩)
include hy
lemma covers_parcel: CoveredAt Ξ (parcel u p f' U) p A price₀ α:= EstFactor.product (zero_le_one.trans hu.effort) hy (postAt U hu he hp ht)
omit hu hy
variable (hq:Quoted Ξ M w θ ρ α A γ u t)
include hq
lemma wallets (i:Head S)(hi:i∈p): EstFactor Ξ i ((payloadT u p f' U i).difference (payloadT t p f' U i)) A (γ*(a' i)) α:= by
   unfold payloadT rateLeaf; split; next h=> exact hq.bill _ _ (decorOrder_lt ht _) i (hp i hi)
   next hx=>
     intro F X v s b χ hh heH E _ _ _ V x hx' hK
     have h:=he _ (mem_sdiff.mpr ⟨hi,hx⟩) F X v s b χ hh heH E V x hx' hK
     have hr: v∈ X.catastrophe (o.ξ/2) R.beta (blaze ({i}:Molecule S)):= by rw [Mayer.noBlaze (hp i hi)]; exact fun w hw=> False.elim (notMem_empty w hw)
     rw [Set.indicator_of_mem hr] at h ⊢
     refine Brush.zi (Eventually.of_forall fun z=>?_) (mul_nonneg hq.defect h.nonneg) h.pos; simp [Insert.gap]
include hy
lemma devotes : CoveredAt Ξ ((parcel u p f' U).difference (parcel t p f' U)) p A (γ*p.card*price₀) α := by
   intro F X z' hX hK hχ hM hH E _ _ _ V x hh ha
   let f (u t' ) y := (payloadT u p f' U t').value (vary X (V y)) (course X A R.beta z' (V y)); let Z i:= stampFactor H i α
   have hr i (hi:i∈p):z'∈X.catastrophe (o.ξ/2) R.beta (blaze ({i}:Molecule S)) := by rw [noBlaze (hp i hi)]; exact fun w hw=>False.elim (notMem_empty w hw)
   have hh' (i) (hi:i∈p): Healthy (Pressure.temp s) (H.supportP i) X.V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) hH
   have hF u (hv: Priced Ξ M w θ ρ α A u) i (hi:i∈p): Brush j (a' i) (Z i) (f u i) x:=by
      simpa only [Set.indicator_of_mem (hr i hi)] using! postAt U hv he hp ht i hi F X z' hX hK hχ hM (hh' i hi) E V x hh ha
   have hD i (hi:i∈p) : Brush j (γ * a' i) (Z i) (fun y=>f u i y-f t i y) x:=by
      simpa only [Set.indicator_of_mem (hr i hi),Insert.gap] using! wallets U he hp ht hq i hi F X z' hX hK hχ hM (hh' i hi) E V x hh ha
   rw [Set.indicator_of_mem (bare p hp X z')]; simp_rw [Insert.gap]
   apply (Telegraph.fades p (hF u hq.gradeP) (hF t hq.gradeF) hD).climb le_rfl
   unfold Z stampFactor; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Utopia.worthy p hy) (zero_le_one.trans hq.gradeP.effort)
end goodK
end Retain
end YM.RGLocalTaylor
