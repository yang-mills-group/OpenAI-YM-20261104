import YM.RGLocalTaylor.Retain.Texture
/-!
# Accounts meter: pays even comparing inherited log-effective reserve from two
stencils, cost relative to full discounted clock, including labels with
mark data. This is on the canonical Ready-Receipt representation.
Doesn't assume Taylor ∂ expansion in bare coupling of an angle-algorithm
itself. Apply local E feedback in later file.
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
open Mayer RG01.Survive Laminate goodK
namespace Mill

variable (H)
variable (W':Team R)(p:Molecule S) {M : ℕ} (τ:Orders M) (t : Stencils T M)
set_option quotPrecheck false
local notation "U'" => p \ W'.signs S
local notation "g'" => Laminate.coverWeight W' S
local notation "f'" => Laminate.partner W' H
local notation "χk" => (χ)

def Tall (H : Cash W s μ L Q o C T R)(W':Team R)(p:Molecule S)(u:Stencils T M)(τ:Orders M) : Config G c→ℝ:= if Start p ∧ W'.signs S⊆p ∧ τ.val ≤ M then validity H p (p\W'.signs S) u (Laminate.partner W' H) (χ:=χ) τ.val else 0

def Total (H : Cash W s μ L Q o C T R)(p:Molecule S) (u:Stencils T M)(τ:Orders M): Config G c→ℝ:= if Start p ∧ τ.val ≤ M then validity H p p u (leg H (own p)) (χ:=χ) τ.val else 0

-- no changing models shifts issued horizon. keep across the actual history.
lemma roleMark (ht:τ.val≤M): Tall H W' p (physical H M) (χ:=χ) τ= column W' p H (χ:=χ) M τ:= by
   unfold Tall column Laminate.scopeM; simp only [if_neg (show τ.val≠M+1 by omega), ht, and_true]; by_cases hp : Start p <;> by_cases hv: W'.signs S⊆p <;> simp only [hp,hv,and_true,and_false, ite_true, ite_false] ; rfl
lemma roleBase (p:H.ThinP) (ht:τ.val≤M) : Total H p.val (physical H M) (χ:=χ) τ= issue H χ M p τ:= by
    unfold Total Mayer.issue atLeaf; rw [if_neg (show τ.val≠M+1 by omega)]; simp only [ht,and_true]; rfl

-- equivalence of unmarked special case, retaining ONLY for proved
-- correspondence in the computations. Use as proof, not agreement of
-- later stencil.hard.
def idle (R:Rep G f): Team R:= ⟨∅, by simp⟩
lemma validity_flat (t: Stencils T M)(f f₀ : Head S→ Insert T)(n:ℕ) : validity H p p t f (χ:=χ) n=validity H p p t f₀ (χ:=χ) n:= by
   have hh U : parcel t p f (z:=p) U= parcel t p f₀ U:= by
      change Insert.mk _=Insert.mk _; congr! 1; funext K X z; exact prod_congr rfl fun i hi=> by simp only [payloadT,dif_pos hi]
   unfold validity; simp_rw [hh]
lemma metBase : Total H p t (χ:=χ) τ= Tall H (idle R) p t (χ:=χ) τ:=by
   unfold Total Tall; simp_rw [show (idle R).signs S=∅ from by simp [Team.signs,idle], empty_subset, true_and, sdiff_empty]; -- edit
   split <;> first| exact validity_flat ..|rfl

-- A-Support BASE & inflated receipt. charge any sector-tag.
def Vbill (H: Cash W s μ L Q o C T R)(W':Team R)(p:Molecule S) (f:Head S→ℝ) (j l:ℕ)(e uJ α θ:ℝ) := if authorized H p ∧ W'.signs S⊆p then speedBill e uJ α j * (W'.weight*(∏ i∈p\W'.signs S, f i))*(1+H.shapeW p)^(l+j)* Mayer.marking H p * θ^p.card else 0

def billBase (H: Cash W s μ L Q o C T R)(p:Molecule S) (f:Head S→ℝ) (j l:ℕ)(e uJ α θ:ℝ) := Vbill H (idle R) p f j l e uJ α θ
local notation "aw" => Tall H W' p (χ:=χ)

variable {θ ρ α γ e discount uJ vJ:ℝ} {w : Head S→ℝ} {u : Stencils T M} {t}
   {N : Captain H j C' d v Y A b r B q n χ}
   (hA:Awning H N.conduit A b discount e uJ vJ k l)
   (hu:Priced N.conduit M w θ ρ α A t)(hq:Quoted N.conduit M w θ ρ α A γ u t)
   {V: Config G c}
   (hh:(roster p).flags=∅)(hC: Healthy (Pressure.temp s) (H.unionP p) V)
   (hv:vJ≤α)
local notation "Ξ" => N.conduit
local notation "b'" => Vbill H W' p w j l e uJ α (creditStencil M θ ρ)
local notation "Δ" => speedBill e uJ α j*older p (U') g' w*(1+H.shapeW p)^(l+j)
local notation "t₀" => (creditStencil M θ ρ)^p.card

include hu
lemma height : 1 ≤ creditStencil M θ ρ:=one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) (one_le_mul_of_one_le_of_one_le one_le_two (one_le_mul_of_one_le_of_one_le hu.value hu.scale))
include hA
lemma invoice_base : 0≤b':= by
   unfold Vbill; split; next=> have he:=hA.earn; have hv:=H.positive_volume p; have hS:=hA.bSc; have hy:=hu.effort; have ht:=W'.profit; have hx:0≤∏ i∈U', w i:=prod_nonneg fun i _=>hu.nonneg _; have hh:=height (H:=H) hu; unfold speedBill Mayer.marking; positivity
   rfl
lemma fee (ht:authorized H p)(hp:W'.signs S⊆p): Δ*t₀ ≤ b':=by
   have hh (i) (hi:i∈ p\U') := Laminate.partnerFit (M:=W') (H:=H) (j:=j) ((Laminate.compartments W' p hp) ▸ hi)
   have hv:0≤ Δ := by
      have he:=historical hu (fun i hi=>(hh i hi).2); have hS:=hA.bSc; have hW:= hA.earn; have ht:=H.positive_volume p; have hy:=hu.effort; unfold speedBill; positivity
   unfold Vbill; rw [if_pos ⟨ht,hp⟩,← Laminate.coverTotal W' S]; apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans (height H hu)) _)
   apply (le_mul_of_one_le_right hv (marking_ge ..)).trans_eq; unfold older; rw [compartments W' p hp]
omit hA in
lemma bounded : GaugeInvariant (Tall H W' p t (χ:=χ) τ) ∧ Measurable (Tall H W' p t (χ:=χ) τ) ∧ LocalOn (H.unionP p) (Tall H W' p t (χ:=χ) τ):=by
   unfold Tall; split
   next ht=>exact identityBook hu (fun i hi=>(partnerFit ((compartments W' p ht.2.1) ▸ hi)).1) ht.1 ht.2.2
   exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩

omit hu in
lemma affordability (hv:vJ ≤ α)(he:W'.signs S ⊆ p)(i:Head S)(hi:i∈p\U') : EstFactor N.conduit i (f' i) A (g' i) α:=by
   rw [compartments W' p he] at hi
   obtain ⟨i,hy,rfl⟩:= mem_image.mp hi; unfold coverWeight partner; rw [chosenAt W' _ _ _ i hy,chosenAt W' _ _ _ i hy]; exact (afford hA i).weaken le_rfl hv

include hv hh hC
lemma applause : Ore V (Tall H W' p t (χ:=χ) τ) v ((ρ^τ.val)⁻¹*b') j:=by
   intro E _ _ _ X x ho hz
   have ht:=invoice_base H W' p hA hu; have hr := hu.scale; have hD : 0≤ (ρ^τ.val)⁻¹*b' := mul_nonneg (by positivity) ht
   unfold Tall; split; next he=>
      have hp := he.2.1
      by_cases ht':authorized H p
      · have hf i (hi:i∈ p\U'):= partnerFit (H:=H) (j:=j) (compartments W' p hp ▸ hi)
        apply (printed_book hA hu (affordability H W' p hA hv he.2.1) (fun i hi=>(hf i hi).2) (fun i hi=>(hf i hi).1) he.1 sdiff_subset ht'.2 hh hC he.2.2 E X x ho hz).climb _ le_rfl
        rw [mul_assoc ((ρ^τ.val)⁻¹)]; exact mul_le_mul_of_nonneg_left (fee H W' p hA hu ht' hp) (by positivity)
      exact Brush.zi (Eventually.of_forall fun x=> Finset.sum_eq_zero (fun i _=> Insert.onLog_of_forbidden ht' _ _)) hD zero_le_one
   exact Brush.zi EventuallyEq.rfl hD zero_le_one
omit hu
include hq
lemma responsive : Ore V (Tall H W' p u (χ:=χ) τ - Tall H W' p t (χ:=χ) τ) v (γ*((ρ^τ.val)⁻¹*b')) j:=by
   have hu:= hq.gradeF
   intro E _ _ _ X x ho hz
   have ht:=invoice_base H W' p hA hu; have hr := hu.scale; have hD : 0≤ γ*((ρ^τ.val)⁻¹*b') := mul_nonneg hq.defect (mul_nonneg (by positivity) ht)
   unfold Tall; split; next he=>
      have hp := he.2.1; by_cases ht':authorized H p
      · have hf i (hi:i∈p\U'):= partnerFit (H:=H) (j:=j) (compartments W' p hp ▸ hi)
        apply (priced_ledger hA hq (affordability H W' p hA hv he.2.1) (fun i hi=>(hf i hi).2) (fun i hi=>(hf i hi).1) he.1 sdiff_subset ht'.2 hh hC he.2.2 E X x ho hz).climb _ le_rfl
        rw [mul_assoc ((ρ^τ.val)⁻¹)]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (fee H W' p hA hu ht' hp) (by positivity)) hq.defect
      exact Brush.zi (Eventually.of_forall (fun x=> (sub_eq_zero_of_eq ((sum_eq_zero (f:=_) (fun i _=> Insert.onLog_of_forbidden ht' _ _)).trans (sum_eq_zero (fun i _=>Insert.onLog_of_forbidden ht' _ _)).symm)))) hD zero_le_one
   rw [sub_zero]; exact Brush.zi EventuallyEq.rfl hD zero_le_one
end Mill
end Retain
end YM.RGLocalTaylor
