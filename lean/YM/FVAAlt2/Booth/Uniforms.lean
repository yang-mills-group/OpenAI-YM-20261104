import YM.FVAAlt2.Booth.Bank
/-! # Ward and rank of full output, ordinary price & raw fuel

Renderer consumes Ward of these complete prescriptions. We obtain it NOT from independent film.Stencils or assuming polymer applies but finite period `@Bulk.Symmetry` on same kernel & receipt + pricing proofs here. Common t angular orientation. NOTE price.t ≠ loop sign.Lia. Vacuum always strip just extensive ledger.out (and true price earn constants in normalization; through ℓ vacuum unnormalized log weapons). -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth.Uniforms
open Function Finset MeasureTheory Filter Set Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Deck Motion Matrix Prim PertExtension Series Series.Radial Series.Tested Chart Lattice Tree Gauge Binding Diagram Diagram.Formal RG Wilson Oracle Geometry Quadratic
open PowerSeries Exterior Precision Bid Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral
open FreeResolvent (tensor flatten)
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix Matrix.Norms.Frobenius
variable {c f n:Side}{G:Gauge}{p: RG.Clip}{O:ChartRatio G}{U:PathData G}
variable (S:StepData c f)(F:Forest S.ratio) (L: Binding.Scale) (K: Comparison.RG02.Bulk.Kernel S p U O)(C:UnitCost) (w:Geometry.Field.Square F)
open Marker Multi Comparison.RG02.Order Comparison.RG02.Moving Comparison.RG02.Moving.Path
open Comparison.RG02.FVAAlt2.Lyric Arm
variable (Z: Branchix→Orders (KFoot G))
variable (V W:Orders (Pin f G))
variable {I:Type}[DecidableEq I]{R:Marker.Census I}
variable (T:Colors R G f)

def cloth (p:RG.Clip)(P:PathData G)(V:Orders (Pin n G)) : Display ( fieldDir G n 1 ):=fun i x=> (if i=0 then -(↑(Assembly.jet (mainTerm p P ∘ represent) 2 x):ℂ) else 0)+(↑(coeff i (flavor 2 (flatten x) V)):ℂ)
def cuff (V:Orders (Pin n G))(m:ℕ): Display (fieldDir G n 1):= fun i x=> ( ↑( coeff i (flavor m (flatten x) V) ):ℂ )
-- Body certificate fields for renderer use
abbrev ceiling (m:ℕ)(i:ℕ) : ℤ:= ↑(i+m)
structure Valid {Z:Type} [NormedAddCommGroup Z][NormedSpace ℝ Z] (p:Display Z) (r m:ℕ):Prop where -- or Z field for Sheet.special.T.Per
    heft i: i≤ r→ Valence.Level (↑(i+m):ℤ) (p i)
structure Bright (V:Orders (Pin f G)) (U:PathData G) (p:RG.Clip) (r:ℕ) : Prop where
    paid : Vacuum V
    paved : gradedSymmetric V
    valid : Valid (cloth p U V) r 2
    sheet : Symmetry.Orbit.Sheet r (cloth p U V)
structure Glyph (V:Orders (Pin f G))(r m:ℕ) : Prop where
    grade e:Within (e+m) (V e)
    paved : gradedSymmetric V
    valid : Valid (cuff V m) r m
    sheet : Symmetry.Orbit.Sheet r (cuff V m)
variable {p' :RG.Clip}{U':PathData G}
local notation "P'"=> scriptV S F K Z V
local notation "P"=> Arm.OutputV S F K Z V
variable (r:ℕ)[Fintype I]
local notation "J"=>directive S
local notation "X"=> fieldDir G c 1
variable (hC: Ribbon.Align r L C) (hs: Prim.Sphere S F L Z)(hV:Arm.Simmer p U C T V r)
variable (D:BudgetPoint)(B:Bed)(hb: YM.FVAAlt2.Period.Rent.Right p U f B)
variable (hc:∀ x:fieldDir G c 1, Bulk.infrared S p U F (directive S) (K.b F) x= Assembly.jet (mainTerm p' U' ∘ represent) 2 x)
local notation "V₀" => cloth p' U' P
local notation "V₁"=> born (Symmetry.Orbit.ground K F J T r) C 0 r
local notation "P₀"=> motion (fun t=> ( Aperture.earn F (G:=G) C t:ℂ ))
include hC hs hV D w hb
include hc in
lemma contact (x:X)(i:ℕ)(hi:i≤r) : V₀ i x=(V₁ i x+ P₀ i)-(↑(coeff i (Binding.out P')):ℂ):=by
    have he:= Aperture.posts_vac K F J C T x r D hV.certified B hb i hi; rw [Arm.accounted S F L K C w Z V T r hC hs hV x B hb i hi] at he; have hx:= hc x
    unfold Symmetry.price at he; rw [hx] at he; rw [← he]; unfold cloth; ring
-- resource gauge Pat sheet. scalar powers. bookkeeping with equivalences χν. 
omit hC hs hV D w hb in
private lemma spark {Φ Q: Display (fieldDir G c 1)} (H: Symmetry.Orbit.Sheet r Φ) (p:ℕ→ℂ) (h:∀ i≤r,∀ x,Q i x=Φ i x+p i): Symmetry.Orbit.Sheet r Q:=by
    constructor
    · intro i hi; rw [ _root_.funext (h i hi) ]; exact (H.known i hi).add contDiff_const
    intro x y hw hx hy i hi
    have ht (x:ℝ→fieldDir G c 1)(hx:Symmetry.glows x) : Symmetry.Orbit.patrol i Q x = Symmetry.Orbit.patrol i Φ x + p i:= by
       unfold Symmetry.Orbit.patrol; rw [sum_congr rfl (g:=fun k:ℕ=> motion (Φ (i-k) ∘ x) k + (if k=0 then p i else 0)) (fun k hk=> ?_),sum_add_distrib,sum_ite_eq',if_pos (Finset.mem_range.mpr (by omega))]; -- finish
       have hh : i-k≤r:= le_trans ( Nat.sub_le .. ) hi; rw [ _root_.funext (h (i-k) hh) ]; unfold Function.comp; dsimp only; rw [Moving.Shift.madd (f:=fun t=>Φ (i-k) (x t)) ( (H.known _ hh).contDiffAt.comp _ (hx)) contDiffAt_const, Moving.Shift.mconst ]; split_ifs with hv; · subst k; rfl
       rfl
    rw [ht x hx, ht y hy,H.follows x y hw hx hy i hi]
include hc in
lemma clear : Bright P U' p' r := by
    let p:=Symmetry.Orbit.ground K F J T r; let H':= LocalScript.stays K D F J T C r hV.certified; let s₁ (i:ℕ):= P₀ i- (↑(coeff i (Binding.out P')):ℂ)
    have hm (i:ℕ)(hi:i≤r)(x:X): V₀ i x= V₁ i x+s₁ i:=by rw [contact S F L K C w Z V T r hC hs hV D B hb hc x i hi]; unfold s₁; ring
    constructor
    · exact Binding.eraseVac _ (Binding.draftedVac _ _ _ (Binding.warmed _ _ ( Arm.trusted S F L C Z V T r hs hV )))
    · exact Binding.erased _ (Binding.colorful _ _ _)
    · have he:Charge r (ceiling 2) p:=fun i hi=> by have ht:= LocalScript.rank K F J T r i hi; unfold ceiling; exact_mod_cast ht
      refine ⟨fun i hi=>?_⟩ -- space
      rw [ _root_.funext (hm i hi) ]; exact ( Adjacent.affordable 0 r he C ( fun i j (hv:i≤j)=> by unfold ceiling; omega) i hi ).add (( (Valence.Level.constant _) ).promote (p:=ceiling 2 i) (by unfold ceiling; omega))
    exact spark r H' s₁ hm
-- mark.Amount m through motive. natural γ parity later.SpecMark.real
variable (m:ℕ)(i:I)(hW:Arm.Single C T W i r m)
local notation "W₁"=> OutputM S F K Z V W m
local notation "W₀"=> (cuff W₁ m)
local notation "u₀"=> born (Symmetry.Orbit.words K F J T r (R.fire i)) C 0 r
include hW
lemma token(e:ℕ)(he:e≤r): W₀ e= (u₀) e:=by
   funext x; have hp:=Aperture.posts_mark K F J C T x r D (R.fire i) hV.certified B hb e he; rw [ Arm.known S F L K C w Z V W T r hC hs hV x B hb i hW e he ] at hp; exact hp
lemma upright (hh : T.power (Arm.pub i)= m) : Glyph W₁ r m:=by
    let p:= Symmetry.Orbit.words K F J T r (R.fire i); let Q:= born p C 0 r
    have ht : Charge r (ceiling m) p:=by
       intro i hi; unfold ceiling; rw [← hh]; exact Valence.solo K F J T _ _
    have hv : Symmetry.Orbit.Sheet r Q:= Call.certified 0 r ht C (Symmetry.Orbit.colored K D F J T r (R.fire i) hV.certified)
    have he:= token S F L K C w Z V W T r hC hs hV D B hb m i hW
    constructor
    · exact Binding.inked _ _ _ (Cluster.end_ranks m true (Cluster.ranks_offer _ _ hW.grade) ( Arm.trusted S F L C Z V T r hs hV )) -- argument exact
    · exact Binding.colorful _ _ _
    · refine ⟨fun j hj=>?_ ⟩; rw [show cuff W₁ m j= Q j from he j hj]; exact affordable 0 r ht C (fun i j (hi:i≤j)=> by unfold ceiling; omega) j hj
    refine spark r hv 0 (fun j hj x=>?_); rw [show cuff W₁ m j= Q j from he j hj,Pi.zero_apply,add_zero]
-- Downstream Run applications supply the hypothesis hc.
end YM.RegulatorIR.FVAAlt2.Booth.Uniforms
