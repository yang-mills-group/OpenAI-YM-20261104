import YM.LocalTaylorR2.Graft1.Level
import YM.LocalTaylorR2.Graft1.Tow
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
open Tail Blush Next.Foundations Planned.GuardedAtom
open Ovens Extra.Histories Progress.DirectedRecipe YM.Planned
variable {v r B w σ a e s' δ : ℝ}{A':BudgetPoint}{l0 q η : ℝ}
-- apply `Canvas` only to available shape.H.P. Profile at output.Raw value
section banded
variable {ι: Type} (P : BudgetPoint)(c':Site c) (J:ι→Support c)
    {f g:ι→ Config G c→ℝ} (t:ℝ)
structure Coast (f :ι→ Config G c→ℝ) (k:ℝ) : Prop where
    ocean : ∃ a:ι→ℝ, (∀ i,P.Regular (J i) (f i) ∧ P.supBounds c' (J i) (f i) (a i)) ∧ SumBudget (fun i=>Push.Local.reservedMass P (J i) (a i)) k
variable (h:Coast P c' J f e)
namespace Coast
open AnalyticBridge
include h
lemma enlarge (he:e ≤ Λ): Coast P c' J f Λ:=by constructor; obtain ⟨a,hp,h⟩:=h.ocean; exact ⟨a,hp,budget_loosen h he⟩
lemma scale : Coast P c' J (t • f) (|t| *e):=by
    obtain ⟨U,hU,h⟩:= h.ocean; constructor; refine ⟨fun i=> |t| * U i,fun i=> ⟨CouplingShape.reg_scale _ (hU i).1,CouplingShape.sup_scale _ (hU i).2⟩,?_⟩
    convert! budget_scale (abs_nonneg t) h using 1; ext i; unfold Push.Local.reservedMass; ring
variable (hp:Coast P c' J g t)
include hp
lemma sub : Coast P c' J (f-g) (e+t):=by
    obtain ⟨D,hD,h⟩:= h.ocean; obtain ⟨U,hU,hp⟩:= hp.ocean; constructor; refine ⟨D+U,fun i=> ⟨CouplingShape.reg_sub (hD _).1 (hU _).1,CouplingShape.sup_sub (hD i).1 (hU i).1 (hD i).2 (hU i).2⟩,?_⟩; simpa only [Local.reservedMass,Pi.add_apply,mul_add] using! budget_plus h hp
lemma add : Coast P c' J (f+g) (e+t):= by
    convert! Coast.sub _ _ _ _ h (Coast.scale _ _ _ (-1) hp) using 1 <;> simp
lemma germ (he:∀ i U, Healthy P.threshold (J i) U→ Reel.memo U (f i)= Reel.memo U (g i)): Coast P c' J g e:=by
  obtain ⟨U,hU,h⟩:= h.ocean; obtain ⟨D,hD,-⟩:= hp.ocean; constructor; refine ⟨U,fun i=>⟨(hD i).1,(hU i).2.1,fun V hv l hl ht=>?_⟩,h⟩; rw [← AnalyticBridge.LocalGaussian.identical (Filter.Germ.coe_eq.mp (he i V hv))]; exact (hU i).2.2 V hv l hl ht
omit hp h
open AnalyticBridge.VerifiedReset
lemma nil : Coast (G:=G) P c' J 0 0:= by
    constructor; refine ⟨0,fun i=>⟨?_,?_⟩,?_⟩; exact reg_const (p:=P) 0; simpa only [abs_zero] using! (sup_const (G:=G) (p:=P) (o:=c') (X:=J i) 0); simp [SumBudget,Local.reservedMass]
lemma all {J':Type}(T:Finset J')(f:J'→ ι→ Config G c→ℝ)(p:J'→ℝ)(h:∀ j∈T,Coast P c' J (f j) (p j)): Coast P c' J (∑ j∈T,f j) (∑ j∈T,p j):=by
  induction T using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; exact nil ..
  | insert i T hi ih=> rw [sum_insert hi,sum_insert hi]; exact add _ _ _ _ (h i (mem_insert_self ..)) (ih fun _ hj=> h _ (mem_insert_of_mem hj))
-- with actual `Coast` routing ALL features
open Reel
lemma strandsP (f: Strand→ ι→ Config G c→ℝ)(z:Strand)(h:∀ i, Coast P c' J (f i) e)(hf:∀ i U,Healthy P.threshold (J i) U → Filled ⊤ j Strand.dial (fun q=>memo U (f q i)))(hz:0≤ Strand.dial z): Coast P c' J (f Strand.bud-f z) (Strand.spelling j*Strand.dial z*e):=by
    let y(i:Fin (j+1)):=f (Reel.Strand.stems i); let a(i:Fin (j+1)):= Strand.tolling z i; have ha:0≤e:= by obtain ⟨a,hF,hB⟩:= (h z).ocean; exact budget_nonneg hB
    have hx := Coast.all P c' J univ (fun i=> a i • y i) _ (fun j _=> Coast.scale _ _ _ _ (h _)); have hU (i:ι) (U:Config G c)(hp:Healthy P.threshold (J i) U): (memo U) ((∑ i,a i • y i) i)=memo U ((f z-f Strand.bud) i):=by
       simp_rw [Finset.sum_apply,map_sum,Pi.smul_apply, memoScale,Pi.sub_apply,map_sub]; exact (Strand.rates z (hf i U hp)).symm
    simpa using! Coast.scale _ _ _ (-1) (Coast.enlarge P c' J (Coast.germ _ _ _ _ hx (sub _ _ _ _ (h z) (h Strand.bud)) hU) ((Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right (Strand.legacy z hz j) ha)))
end Coast
end banded
end YM.LocalTaylorR2.Marker
