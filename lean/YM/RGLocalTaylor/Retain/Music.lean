import YM.RGLocalTaylor.Retain.Woven
/-!
# Receipt across the Meet supports for TWO spatial Price budgets (heat/mark)
After holding sector emissions, apply telescoping price and reserve,
including whole kernels with Aura Fragrance BEFORE pane projections. Seats
appointments allow reading anchored Real/O (paid logarithmic exponent) and
Fee. No assertions of aperture owner. These very rates still need to fit
coarse and final λ budget. Based on Cadre/Songs & Mayer&Laminate proofs,
still requires these costs be paid with Booth.Permission. Not granting
any independent profile consumes these receipts without explicit guarantees.
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt Blaze.March
namespace Retain
open RG01.Survive Mayer goodK Trees Merge Palette Fort Laminate
namespace Mill
open Ursell Gas
open Captain
variable {m M :ℕ} {p:Molecule S} {e vJ uJ K θ α β Z γ δ δ' κ r' d' ρ:ℝ} {AΦ AΨ :Stencils T M}
   {Ξ : Utopia H j v d r C' χ} {g: Head S→ℝ}
   {N : Captain H j C' d v Y A b r B q n χ}
   {ι: Type} [Fintype ι]
   {boxes coins:ι→ℕ}

abbrev Scans (ι:Type)(H : Cash W s μ L Q o C T R) := H.ThinP → ι → Config G c → ℝ
structure Verse (H: Cash W s μ L Q o C T R)(boxes coins:ι→ℕ)(Θ :Scans ι H)(a w r:ℝ)(j:ℕ) (f:H.ThinP→ι→ℝ)(g:H.ThinP→ℝ) :Prop where
    heft : 1 ≤ a
    pays : 1 ≤ w
    live : ∀ i j, 0 ≤ f i j
    PriceBox i : ∑ j, 2*f i j*(a^boxes j*w^coins j) ≤ g i
    lyric i j': GaugeInvariant (Θ i j') ∧ Measurable (Θ i j') ∧ LocalOn (H.smallAt i) (Θ i j')
    cheap i j' U (_:Healthy (Pressure.temp s) (H.smallAt i) U): Ore U (Θ i j') r (f i j') j
structure Cooperates (H : Cash W s μ L Q o C T R)(boxes coins:ι→ℕ)(Θ Θ': Scans ι H)(a w r:ℝ)(j:ℕ)(f:H.ThinP→ι→ℝ)(g:H.ThinP→ℝ)(α:ℝ) :Prop where
    formalP : Verse H boxes coins Θ a w r j f g
    realP : Verse H boxes coins Θ' a w r j f g
    profit : 0 ≤ α
    rights i j' U (_:Healthy (Pressure.temp s) (H.smallAt i) U) : Ore U (Θ i j'-Θ' i j') r (α*f i j') j
variable {f₁:H.ThinP→ι→ℝ}{g' : H.ThinP→ℝ}{Θ Θ': Scans ι H} (h : Verse H boxes coins Θ ρ κ v j f₁ g') (ht: Cooperates H boxes coins Θ Θ' ρ κ v j f₁ g' γ)
   (z:H.fragrances)

abbrev lot (z:H.fragrances)(ι:Type):= (Option (Fin z.fst))→ι
def dots (f:ι→ℕ)(z:H.fragrances)(u:lot z ι):ℕ:=∑ i,f (u i)
abbrev printed (f: Scans ι H)(z:H.fragrances)(u:lot z ι)(V:Config G c):= Laminate.tax z * (∏ i, f (z.2 i) (u i) V)
abbrev meet_bill (g:H.ThinP→ι→ℝ)(j:ℕ)(z:H.fragrances)(u:lot z ι):= (∏ i,(2^j:ℝ)*(2*g (z.2 i) (u i)))
set_option quotPrecheck false
abbrev salary (g:H.ThinP→ι→ℝ)(j:ℕ)(z:H.fragrances)(u:lot z ι):= ‖Laminate.tax z‖*meet_bill g j z u
variable (u : lot z ι)
local notation "t'" => salary f₁ j z
local notation "u'" => meet_bill f₁ j z
local notation "uJ'" => H.smallAt
local notation "c'" => reachability (H:=H)
local notation "F" => printed Θ z
local notation "F₀" => printed Θ' z

include h
lemma reshaped : GaugeInvariant (F u) ∧ Measurable (F u) ∧ LocalOn (reachability z) (F u):= by
   let x:= Laminate.tax z; have he i:= h.lyric (z.2 i) (u i); have hh i: uJ' (z.2 i) ⊆ c' z:= subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ i)
   exact ⟨fun t U=> congr_arg (x *·) (prod_congr rfl fun i _=> (he i).1 t U),measurable_const.mul (Finset.measurable_fun_prod _ (fun i _=> (he i).2.1)),fun U V hu=> congr_arg (x *·) (prod_congr rfl fun i _=> (he i).2.2 U V (agrees_mono hu (Finset.coe_subset.mpr (hh _)) ))⟩

lemma wages :0≤ meet_bill f₁ j z u:= prod_nonneg fun i _=> by have ht:=h.live (z.2 i) (u i); positivity
lemma salary_pos :0≤ t' u:= mul_nonneg (norm_nonneg _) (wages h z u)
omit h [Fintype ι] in
lemma total (f:ι→ℕ) (x:Option (Fin z.fst)): f (u x) ≤ dots f z u:= single_le_sum (f:=fun x=> f (u x)) (fun _ _=>Nat.zero_le _) (mem_univ x)
-- omit h
variable {V : Config G c} (hp: Healthy (Pressure.temp s) (reachability z) V)
include hp
lemma paid_value : Ore V (F u) v (t' u) j:=by
   intro E _ _ _ U x hx hh
   have hv i: Healthy (Pressure.temp s) (H.smallAt (z.2 i)) V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ i)) hp
   let f(i:Option (Fin z.fst)) (t:ι)(x:E):= Θ (z.2 i) t (U x)
   refine ((Products.earns f (fun i=>f₁ (z.2 i)) (fun i t=>h.cheap _ _ _ (hv i) E U x hx hh) u).climb ?_ le_rfl).smul (Laminate.tax z) -- .. args hx?
   refine Finset.prod_le_prod (fun i (_:i∈ (univ:Finset _))=> mul_nonneg (by positivity) (h.live _ (u i))) (fun i _=> mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (h.live _ _) one_le_two) (by positivity))

omit h
include ht
lemma meet_error : Ore V (F u - F₀ u) v (γ*t' u) j:=by
   intro E _ _ _ U x hx hh; let w:=Option (Fin z.fst); let K:ℝ:= Laminate.tax z
   let f (Θ :Scans ι H)(i:w) (t:E):= Θ (z.2 i) (u i) (U t); let Q i:= f₁ (z.2 i) (u i); let S:= Fintype.card (Option (Fin z.fst))
   have h := ht.formalP; have hv i: Healthy (Pressure.temp s) (H.smallAt (z.2 i)) V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ z.2) (mem_univ i)) hp
   have hb (Θ) (h:Verse H boxes coins Θ ρ κ v j f₁ g') (i:w) := (h.cheap (z.2 i) (u i) V (hv i)) E U x hx hh
   have hU : Brush j (γ*meet_bill f₁ j z u) 1 (fun t=> (∏ i, f Θ i t) - ∏ i,f Θ' i t) x:= by
      have hF (i:w):= (ht.rights _ (u i) V (hv i)) E U x hx hh
      refine (Telegraph.fades (t:=w) (α:=γ) (f:=f Θ) (q:=f Θ') univ (fun i _=>hb Θ h i) (fun i _=>hb Θ' ht.realP i) (fun i _=>hF i)).trim.climb ?_ le_rfl
      unfold meet_bill; simp only [card_univ,prod_mul_distrib,prod_const,sum_const,nsmul_eq_mul,mul_one]
      let C:ℝ:= ∏ i:Option (Fin z.fst), Q i; have hC:0≤C:= prod_nonneg fun i _=>h.live _ _
      have hV : S<2^S:= Nat.lt_two_pow_self; have hz: (1+S:ℝ) ≤ 2^S:=by exact_mod_cast (by omega : 1+S ≤ 2^S) -- omega need supply
      have hu : (1+S:ℝ)^j ≤ (2^j:ℝ)^S:= (pow_le_pow_left₀ (by positivity) hz _).trans_eq (by rw [←pow_mul,←pow_mul,Nat.mul_comm])
      change γ*S*C * (1+S:ℝ)^j ≤ γ*((2^j)^S*(2^S*C))
      calc
        _ ≤ γ*2^S*C*(2^j:ℝ)^S := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left zero_le_one).trans hz) ht.profit) hC) hu (by positivity) (mul_nonneg (mul_nonneg ht.profit (by positivity)) hC)
        _ = _:= by ring
   exact ((hU.smul K).shimmy (Eventually.of_forall fun t=>by simp only [Function.comp_apply,printed,Pi.sub_apply, K, f, smul_eq_mul, mul_sub];rfl)).climb (show ‖K‖*(γ* u' u)≤_ from Eq.le (mul_left_comm ..)) le_rfl
end Mill
end Retain
end YM.RGLocalTaylor
