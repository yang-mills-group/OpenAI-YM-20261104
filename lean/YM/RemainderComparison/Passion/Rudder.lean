import YM.RemainderComparison.Passion.Sails
/-!
After c.Ap orientation: rooted adjusted logs retain root *unions incl old
connectors*. Both field-mask evaluations (placing literal Section headers or
expanding mask to all carriers) charged. Every induced commission survives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Passion
open Function Filter Set Finset Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker
open Solos Mosaic Verse Serif Flues WickReps Ethereal Lacuna Lobby
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D :ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I:Type}
variable (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι)
variable {σ b c e :ℝ} (T:Manor G n ι (Audited Q) I)(p:BudgetPoint)(R:ι→Support n)(Z:Set ι) (V:Plane G n θ) (X:Hol G)
variable (M:SeatD.MaskType)(i:Roll T R Z D)
local notation "W₀" => mapWord D
local notation "T₀"=> T.marks i.val.val
local notation "P"=> T.halls i.val.val
local notation "v₀"=> p.threshold
local notation "Ra₀"=> Ra T R Z V i
local notation "P₁"=> SeatD.PairD
set_option quotPrecheck false
open SeatD
-- retain an explicit MODE which interprets canonical only once. grants on both; architecture for Θ joint proof.Hit
local notation "J₀" => Roll T R Z D
local notation "F'" => area T R Z V (D:=D)
open PhysicalNext.Repeat Trio Animals
open Vesuvius PhysicalNext.Repeat Trio Flues
-- R.Guards Aperture.Purchase supports release to LOG. Canon.Track readiness enough to put back on P.K
variable (h:Precepts T p R Z D σ b)(hx:Lodge T p R Z V X M D e)(w d:ℝ)(t:ℕ)(he:AxisG p V X w t d)
local notation "P₀" => p.supportExponent
local notation "S"=> P₀+1
local notation "c₀"=>T.marks
local notation "L₁"=> amount T p R Z V X M (D:=D)
local notation "L₂"=> leakage T p R Z V X M (D:=D)

def Flame (D:ι→Finset θ): Vesuvius G n ι (Roll T R Z D) (Audited Q):=⟨area T R Z V,fun i=>⟨T.port i.val.val,(lanes T R Z V i) (T.call _)⟩, fun b i=> leakage T p R Z V X M i b,fun i=>T.marks i.val.val⟩
local notation "W₁"=> Flame T p R Z V X M D
include h he hx
lemma amendment : Vesuvius.Works p R Z W₁ S 0 (4*e) ∧ Hearth D Z W₁:=by
   have ht i : (W₁).site i = area T R Z V i:=rfl
   obtain ⟨f,hf,hH,hQ⟩:=hx.budget
   refine ⟨⟨fun i a=>nearT T p R Z V X M i a h he,fun i _ k hv _ _=> (rooted T R Z V i).2 k hv,fun i a U he' => literal T p R Z V X M i a h he U he',fun _=>0,fun i=>4*f i,fun _=>le_rfl,fun i=> mul_nonneg (by norm_num) (hf i),fun i=> ?_,Quotes.hit_scale (by norm_num) hH,fun i a U=>?_⟩,⟨fun i _ U _=>scoreLeak T p R Z V X M i h he U⟩⟩
   · simp only [zero_mul,ite_self]; exact budget_of_sum (fun _=>le_rfl) (fun _=>by simp)
   rw [if_neg (show Verse.load Z ((W₁).opus i)≠0 from i.val.prop)]; exact ((hQ i).1 U a).2
local notation "L"=> Lacuna.rudder W₁ Z
variable {α:Audited Q}
variable [DecidableEq θ] {J:Census θ} (z:ι→Poly J) {k:ℕ} {q:θ→ℝ}
variable (U:Config G n)(a: Audited Q)(hZ:Passion.Oriented D J Z z)(hk: Serif.Chorus J q Z z k)
def cash(D:ι→Finset θ) (a:Audited Q) (U:Config G n) (i:Roll T R Z D) : Poly J:= ((Passion.amount T p R Z V X M i a U:ℝ):ℂ) • controls Z z (T.marks i.val.val)
local notation "N₁" => cash T p R Z V X M z D
variable [Countable I] (y:Audited Q)
include hZ hk
lemma title : Summable (cash T p R Z V X M z D a U) ∧ HasSum ((L y).plume Z z a U) (day J Z T p z a U- ∑' i,N₁ a U i):=by
    let B':= W₁
    have hs :0≤ S:= add_nonneg p.exponent_pos.le zero_le_one
    obtain ⟨hw,hL⟩:= amendment T p R Z V X M h hx w d t he
    have ht:= Vesuvius.pi_support p R k a Z z W₁ hw hs hk U
    have hv := Lacuna.flumes W₁ p Z y a R U z hw hs hk
    have hA (v:J₀): v∉ Lacuna.shade W₁ Z:= v.val.prop
    have hW (θ':Seat n): Lacuna.wray W₁ Z y (θ'.view U)=0:=by
        unfold Lacuna.wray; letI : IsEmpty (↥(Lacuna.shade W₁ Z)):=⟨fun i=> hA i.val i.prop⟩; exact tsum_empty
    have hp : Lacuna.mark W₁ Z z a U= ∑' i,Vesuvius.books a Z z W₁ U i:=by
        unfold Lacuna.mark; rw [tsum_subtype_eq_of_support_subset]; intro i _; exact hA i
    rw [show (fun i:Seat n=> Lacuna.wray W₁ Z y (i.view U))= fun _=> (0:ℝ) from funext hW, Lacuna.revolves] at hv
    simp only [Finset.sum_const_zero,mul_zero,Lacuna.tint,Complex.ofReal_zero,zero_smul,zero_add] at hv
    rw [hp] at hv; obtain ⟨f,hf,hH,hF⟩:= hx.budget; have ht' : Summable f:= Yearling.concerns _ _ f hH hs hf (fun i _=> (W₁).yeah i)
    have hV : Summable (N₁ a U):= (Poly.budgeted hk.votes (ht'.mul_left 3) (f:=N₁ a U) (fun i=>by
         unfold cash; rw [Poly.adapted, Complex.norm_real]; exact (mul_le_of_le_one_right (norm_nonneg _) (Serif.bought hk _)).trans ((hF i).1 U a).1)).1
    refine ⟨hV,?_⟩; rw [marches T p R Z h z hZ]
    have hz(i:Roll T R Z D) : T.paint p Z z a U i.val.val = N₁ a U i+ Vesuvius.books a Z z W₁ U i:=by
         unfold Manor.paint Vesuvius.books cash;
         change _ = _ + (↑(T.wet p a i.val.val U- _):ℂ) • controls Z z (T.marks i.val.val); rw [Complex.ofReal_sub,sub_smul]; abel
    simp_rw [hz]; rw [Summable.tsum_add hV ht,add_sub_cancel_left]; exact hv
end YM.RemainderComparison.Passion
