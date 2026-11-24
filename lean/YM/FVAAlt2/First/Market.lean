import YM.FVAAlt2.First.Fit
import YM.FVAAlt2.First.Sum
/-!
# MarkFull PP-style: complete real Wilson marks of the LPT d-row budget.
Same Booked optics as Grind uses for actual Section & MS. Does not
assert that these stencils replace the actual ones or vice versa; here
auxiliary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Draft MS.Menus MS.Local.Physical
open MS.Book MS.Book.Convolve MS.Native.Paint MS.Native.Wilsonian MS.Plane MS.Theater MS.Landau MS.Landau.Detect MS.Lifting MS.Tone MS.Momentum
open Pert Pert.Orb SchemeRG11 SchemeRG11.Atoll SchemeRG11.Haze SchemeRG11.Pile SchemeRG11.Sway
open MvPolynomial
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius PowerSeries Classical
variable {G: Gauge}{d k:ℕ}{F: Frames G}{n:Side}{p q:pLabel G}
local notation "Ω"=> Lane4 G
local notation "Φ"=> Dot G Cover
lemma saw_real(o:Site n)(p:pLabel G)(U:Config G n): Complex.ofReal (sensorMap o p U)= terrain o 1 (realCast p) U:= by
 rw [terrain,Pert.Bare.exactColumn,← Outlook.cabin]; congr 1; unfold sensorMap Outlook.nib; rw [LinearMap.pi_apply]; change aeval _ p=_; apply congrFun (f:=fun q=> aeval (R:=ℝ) (fun i:Key G=> legAt i o U) q) (g:=_) _ p -- simpler
 have he (i:Key G): legAt i o U = Outlook.rune (Pert.Bare.valuesU 1 1 U o) i:=by unfold legAt Outlook.rune Pert.Bare.valuesU; rw [inv_one,one_smul]
 exact funext fun q:pLabel G=>by simp_rw [he]
lemma sensor_open (hp:realCast p∈invariantSpace G) (o:Site n): OpenGauge (drive n) (sensorMap o p) :=by
 intro h U; apply Complex.ofReal_injective; rw [ saw_real,saw_real,terrain,terrain ]; let f:=fun p:Site n=>(h p)⁻¹; rw [show siteGauge (drive n) h U=Lattice.gauge f U from ?_,Bare.exactColumn, show Bare.valuesU 1 1 (Lattice.gauge f U) o=Labels.colored (f o) (Bare.valuesU 1 1 U o) from funext fun i=> by simp [Pert.Bare.valuesU,Labels.colored,Pert.Bare.tensor_gauge]]; exact hp _ _
 ext1; simp [Chart.siteGauge,Lattice.gauge,Chart.endRail,Chart.drive,f]
lemma happened (hp:p.IsHomogeneous k) (he:realCast p∈invariantSpace G) : Studio.Aura (resident p) k:= ⟨ formed_low hp,(parallels p).cost, fun n=>⟨ _, sensor_open he (0:Site n), ((parallels p).born n).born, ((parallels p).born n).home ⟩⟩
-- pure weight sectors
abbrev Orbis(p:pLabel G) (d k:ℕ): Prop:= IsWeightedHomogeneous Labels.bidegree p (d,k)
lemma weightL (h:Orbis p d k): IsWeightedHomogeneous Labels.generation p d := by intro i hi; have hi:= h hi; rw [weight_slot] at hi; exact Prod.mk.inj hi|>.1
lemma weightR (h:Orbis p d k): p.IsHomogeneous k:= by intro i hi; have he:= h hi; rw [ weight_slot ] at he; rw [Finsupp.weight_apply, ← (Prod.mk.inj he|>.2) ]; simp
lemma stroll (c:ℝ) : Fits (resident (G:=G) (C c)) (Theater.orbit G (realCast (C c))) 0 0 false:=by
 rw [formed_C, show realCast (G:=G) (C c)= MvPolynomial.C (c:ℂ) from map_C .., Theater.cus]; rw [ show (coin (c:ℂ):Law G)=(c:ℂ) • coin 1 from (?_) ]; apply Fits.smul _ (Fits.unit)
 funext i; rcases i with _|⟨i,l⟩; · exact Eq.symm (mul_one _)
 exact Eq.symm (mul_zero _)
lemma open_h (h:Orbis p d k): Fits (resident p) (Theater.orbit G (realCast p)) k d false := by
 refine paradigm Labels.bidegree (fun x:ℕ×ℕ=> fun p:pLabel G=>Fits (resident p) (Theater.orbit G (realCast p)) x.2 x.1 false) h ?_ (fun x=>?_) ?_ ?_
 · intro c; exact stroll c
 · unfold realCast; rw [_root_.map_zero,_root_.map_zero,formed_zero]; exact Fits.zero _
 · intro v i f hf h; rw [formed_mul,formed_X]; unfold realCast; rw [_root_.map_mul,map_X,Theater.bags]; change Fits _ _ (1+v.2) (↑(Labels.generation i+v.1):ℤ) false; rw [Nat.cast_add]; exact (stages_One i).take h (first i) ( formed_low (weightR hf) )
 intro v f q _ _ hf hq; rw [formed_add]; unfold realCast; rw [_root_.map_add,_root_.map_add]; exact hf.add hq
-- polymorphism of W corrections
abbrev winds (G:Gauge)(h:ℝ):= ((Atoll.unmarked G h).neg)
lemma utc (p:pLabel G)(h:ℝ): dream h (realCast p)= realCast ((winds G h).heat p):=Dose.mapped_heat ..
lemma harness(p:pLabel G)(i:ℕ): homogeneousComponent i (realCast p) = realCast (homogeneousComponent i p) :=by ext1 d; unfold realCast; rw [coeff_homogeneousComponent, MvPolynomial.coeff_map, MvPolynomial.coeff_map,coeff_homogeneousComponent]; split <;> simp_all
abbrev clip (i:ℕ):=(homogeneousComponent (σ:=Key G) (R:=ℝ) i).comp ((winds G 1).heat) -- `→ₗ`
lemma clipvia(i:ℕ)(he:realCast p∈invariantSpace G): Studio.Aura (resident (clip (G:=G) i p)) i:= happened ( homogeneousComponent_isHomogeneous .. ) (by rw [clip,LinearMap.comp_apply,← harness, ← utc ]; exact SchemeRG11.Sway.homogeneous_inv (SchemeRG11.Sway.dream_inv he _) i)
-- At every n through k. Tone charge assembly. Unit.Prescribed.
abbrev cereal (i:ℕ)(p:pLabel G):= levels i (resident (clip i p))
def total (k:ℕ)(p:pLabel G):= ∑ i∈Finset.range (k+1), cereal i p
lemma span_pay (k:ℕ)(he:realCast p∈invariantSpace G)(i:ℕ): Tune Landau.parity ghostNo 0 ( total k p i ) ∧ Colorless (total k p i)∧Limit (total k p i).val (i+k):=by
 unfold total; rw [Finset.sum_apply]; refine ⟨Tune.sum _ (fun j _=> TuneModel (clipvia j he).phase _), Colorless.csum _ (fun j _=> ColorMod (clipvia j he).lit _), ?_⟩
 rw [sum_stack]; apply Limit.sum; intro j hj; unfold cereal levels; exact Limit.up (Limit.mod _ ((i:ℤ)+j)) (by simp at hj; omega)
lemma whole_price (h:Orbis p d k)(he:realCast p∈invariantSpace G): MarkFull (total k p) (Theater.orbit G (realCast p)) d k :=by
 refine ⟨ ?_, fun i=>(span_pay k he i).1, fun i=> (span_pay k he i).2.1,fun i=>(span_pay k he i).2.2, fun g=>?_⟩
 · unfold Fits total; rw [Finset.sum_apply, _root_.map_sum,_root_.map_sum, sum_eq_single_of_mem k (by simp) ]; · simp only [cereal, levels,clip,LinearMap.comp_apply,high_component _ (weightR h), Tone.grade, Nat.cast_zero,zero_add,Glyph.mask_sq]; exact open_h h
   intro i hi hx; simp only [cereal,levels,Tone.grade,Nat.cast_zero,zero_add]; exact maskOff (by simp at hi; omega) (Limit.mod _ _)
 let W:=actB (Spectrum G)+ blocks (Spectrum G) (core G); change W _= _; rw [total,_root_.map_sum]; exact Finset.sum_eq_zero fun i _=> (clipvia i he).closed g
-- Booked optics ANY fixed. real materials of Letters. Mark.Symbol.
variable {B:Deck G}
def price (u:B.BIndex d k): pLabel G := (Outlook.real_material (Shop.seat B u (d:=d)).val (congr_arg Subtype.val ( Shop.single_p .. )) ).choose
lemma price_is(u:B.BIndex d k) : realCast (price u)= ( Shop.seat B u ).val:= (Outlook.real_material _ (congr_arg Subtype.val ( Shop.single_p B u ))).choose_spec
lemma price_in(u:B.BIndex d k): realCast (price u)∈invariantSpace G:= price_is u ▸ (Shop.seat B u (d:=d)).property.2 -- orientation eq?
lemma price_grade(u:B.BIndex d k): Orbis (price u) d k:= by
 have he : IsWeightedHomogeneous bidegree (realCast (price u)) (d,k):=by rw [price_is]; exact (pure_grade ..|>.1 (Shop.isSeated B u))
 intro i hi; refine he ?_ ; unfold realCast; rw [coeff_map]; change (↑((price u).coeff i):ℂ) ≠ 0; exact_mod_cast hi

def ExtraBook (B:Deck G): RichBook B where
 menu d k i:= total k (price i)
 rich d k i:= ( by have he: Theater.orbit G (realCast (price i))=B.raw d k i := by rw [price_is]; exact lamp_here ..
                   rw [← he]; exact whole_price (price_grade i) (price_in i) )
end YM.FVAAlt2.Pairing
