import YM.Frontier6.Bouquet.Audit.Ribbon
/-!
# Test surfaces. Context valuation and geometry guards.

Working longitudinal widths can be much larger than the transaction cells.
 Use on *each finite aperture family*, before taking any positive radial
 distribution limit. Positions common to all audiences are not stitched between
 different regulators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Audit
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I L V:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {K:Final C F S}{P Q:Ensemble}{d:Slot→ℕ}{M:Pod→ℝ} {s D₀:ℝ}

-- choose cap independent of finer chart. available for every enclosed family
structure Dais (K:Final C F S)(d:Slot→ℕ)(P:Ensemble)(M:Pod→ℝ):Prop where
   pos : ∀ p∈P.enclosed,0<M p
   zenith : ∀ p∈P.enclosed, (p.card:ℝ)*(M p)≤1
   safe : ∀ p∈P.enclosed,Frontier6.Safe K (p.horizon d) (2*M p)
   swell : ∀ p∈P.enclosed,∀ q<p,2*M p ≤ M q
namespace Dais
variable (h:Dais K d P M)
include h
lemma lower (he:Q≤P):Dais K d Q M:=⟨fun i hi=>h.pos i (under he hi), fun i hi=> h.zenith i (under he hi),fun i hi=>h.safe i (under he hi),fun i hi=> h.swell i (under he hi)⟩
end Dais
structure Length (P:Ensemble)(M:Pod→ℝ)(s:ℝ): Prop where
   pos : 0<s
   top : ∀ p∈P.enclosed,2*s≤ M p
lemma Length.lower (he:Length P M s)(h:Q≤P): Length Q M s:= ⟨he.pos,fun _ h'=> he.top _ (under h h')⟩
-- helpers with horizon
lemma card_allowed (he:Dais K d P M)(hx:Length P M s)(i:P)(w:i.val.Horizon d): Frontier6.Safe K w (2*(2*s)):= (he.safe i.val (stage_in i.property)).down K w.isLt.le (mul_le_mul_of_nonneg_left (hx.top i.val (stage_in i.property)) zero_le_two)

-- footprint primitive common Peers. need convex closed? don't require closed; points explicit
structure Aura (P:Ensemble) where
   center : Seats P
   foot : Balcony P
namespace Aura
structure Cozy (A:Aura P)(U:Pod→ℝ):Prop where
   around : ∀ i:P, A.center i∈ A.foot i
   solid : ∀ i:P,Convex ℝ (A.foot i)
   prices : ∀ i:P,∀ u∈ A.foot i, ‖u-A.center i‖≤ U i.val
end Aura

variable (K P)
structure Air (I L:Type)(Y:Type)[AddCommGroup Y][Module ℂ Y] where
   route : Audit.Ribbon I L
   role : P→ L
   region : I→ Aura P
   sky : I→ Patron S P Y
   account : I→ ℝ
-- K implicit? header P not typed? K binder implicit in S but not needed!
variable {K P}
namespace Air
variable {Y:Type} [NormedAddCommGroup Y] [NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (A:Air (S:=S) P I L Y)
def lengths (i:I)(j:P):ℝ:= A.route.length i (A.role j)
lemma length_pos (i:I)(j:P) : 0 < A.lengths i j:= A.route.leg_pos ..
lemma length_cap (i:I)(j:P): A.lengths i j ≤1:=(A.route.covered i _).2
def suitable (i:I)(d s:ℝ):Prop:= ∀ j:P,A.lengths i j≤d*s
def accountCost (v:I→ Y)(i:I):Y:= (A.account i)⁻¹ • v i
def foci {J:Type}(p:J→ I)(j:P): Fabric J:= fun i=> (A.region (p i)).foot j
-- holds for *any* compatible trajectory into this Air. Thickening
-- to nearby tests irrelevant.Ties protected. No assertion uniform for
-- unbounded T length orders or unbounded probes.
def Hosts (K:Final C F S) (A:Air (S:=S) P I L Y):Prop:= ∀ (J:Type)(y:J→ I)(T:Fareway J)[T.via.NeBot] (V:Finset ℝ)(x:L→ℝ), A.route.Speaks T y x→ (0∈V)→(∀ v∈V,0≤v)→(∀ i:P,x (A.role i)∈V)→
    ∀ (u:P→ℝ)(v:P → J→ Spelling S), (∀ i:P, Pen K T V (x (A.role i)) (A.foci y i) (v i) (u i)) → T.Costs (fun i=> (A.account (y i))⁻¹ • A.sky (y i) (fun j=> v j i)) (∑ i:P, u i)
structure Welkin (M:Pod→ℝ): Prop where
   safe : ∀ i:I,(A.region i).Cozy M
   smooth : ∀ i:I,Gentle (A.sky i) (A.region i).foot
   pos : ∀ i:I,0 < A.account i
end Air

section
variable (P) (r:P→ℝ)
def paths : Set Room:= {x:Room|∃ i:P,x∈ Accounts (normal i.val) (r i)}
lemma paths_frame : paths P r⊆ (fiber P :Set Room):=fun i ⟨j,hj⟩=> home_sub j.property hj.1
lemma paths_cost (h:∀ i:P,r i ≤ 1){x:Room}(he:x∈ paths P r):‖x‖≤1:=by obtain ⟨i,hv⟩:=he; exact hv.2.trans (h i)
def lodge (f:Full (fiber P)) (D:ℝ) :Prop:= ∀ p:P, tsupport f⊆ cylindrical (fiber P) (normal p.val) (closedBall 0 (D*r p))
structure Fellow (A:Aura P)(t:ℝ)(f:Full (fiber P))(j:ℕ) (B:ℝ):Prop where
   fair : Fair f A.foot A.center
   local_ : lodge P r f t
   costs : Checks (fiber P) (paths P r) f j B
end
namespace Fellow
variable {f:Full (fiber P)}{A:Aura P}{t:ℝ}{u:P→ℝ}{i j:ℕ}
lemma below (he:Fellow P u A t f i s)(hr:j ≤ i)(hv:s ≤ D₀):Fellow P u A t f j D₀:= ⟨he.fair,he.local_,he.costs.low hr|>.cost_mono hv⟩
end Fellow

-- constant λ current aperture cutoffs, some square log preparation unnecessary
-- for the purely Euclidean result

def common (u:ℝ) : Veins:= if h:0<u then ⟨fun _=>u,fun _=>h⟩ else ⟨fun _=>1,fun _=>one_pos⟩
lemma common_at {u:ℝ}(h:0<u)(p:Pod): (common u).range p=u:=by unfold common; rw [dif_pos h]
lemma horizon_power (i:P): (i.val.horizon d:ℤ)> i.val.arityD d - (dim (normal i.val):ℤ):=by -- types
    unfold Pod.horizon tiers dim; omega
end YM.Frontier6.Bouquet.Audit
