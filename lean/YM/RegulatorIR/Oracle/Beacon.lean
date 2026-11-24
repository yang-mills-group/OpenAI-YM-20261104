import YM.RegulatorIR.Oracle.Frame

/-! Genuine inverse on tree forest. No Rank obstruction even at small tori.
Rates from FULL cover prices committed after L. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {n p:Side} {X Y A V: Type}
-- ledger usage exact. priceL exponential recipe
variable (P:Patch)(K:KernelChoices)(G: Gauge)(B:Precision.Bed)
variable {σ Ω α:ℝ} {S:Clip}
variable (F:Hall B σ Ω α S) (Z:P.Branches K G)

def intensity (P:Patch)(K:KernelChoices)(G:Gauge) (α:ℝ):= min (FreeResolvent.treeFare G P K α) 1
lemma intenseP (F:0<α): 0< intensity P K G α:= lt_min (FreeResolvent.treeFare_pos _ _ _ F) zero_lt_one

include Z
lemma pav : ∃ c:ℝ,∀ n:Side,c≤ n.val→ Bid.Larger (G:=G) (avenue P K n):=by
 let m:=100*(P.radius+4*P.L.val)
 refine ⟨m+100,fun n h=>?_⟩
 have he : m+100 ≤ n.val :=by exact_mod_cast h
 constructor
 · exact Z
 constructor
 · exact le_trans (show m ≤ n.val from by omega) (Nat.le_mul_of_pos_right _ P.L.property)
 omega
include F
lemma arch : ∃ c:ℝ,E_lower c (intensity P K G α) (cousin P K G B) (blockQ G P.L) :=by
 obtain ⟨c,hc⟩:=pav P K G Z
 refine ⟨c,fun p hp=> ?_⟩; rw [touches P K G B F];
 apply FreeResolvent.Shell.gap (A:=FreeResolvent.fullMatrix G _ _) (renter P G p)
 exact FreeResolvent.tree_gap (avenue P K p) (stemF P p) B.metric (hc p hp) F.lip ⟨fun v=> ((F.floorP _).uniform.1 v).1⟩

-- shape $margin adjusted
abbrev nativeL : Type:= Co P.L (PAC G 1)
def gauge_K (σ Ω α:ℝ) := FreeResolvent.margin (nativeL P G) σ ((trunkCost P K G σ Ω).toReal) (intensity P K G α)
def widthK (σ Ω α:ℝ):= gauge_K P K G σ Ω α / 2
def markup (σ Ω α:ℝ) :ℝ≥0∞:= Fintype.card (Co P.L (PAC G 1)) * ENNReal.ofReal (FreeResolvent.inversePrice (Co P.L (PAC G 1)) σ (trunkCost P K G σ Ω|>.toReal) (intensity P K G α) 0 (widthK P K G σ Ω α))
-- omit Z
omit Z in
lemma width_pos :0 < widthK P K G σ Ω α:=half_pos (FreeResolvent.margin_pos (Co P.L (PAC G 1)) F.pos ENNReal.toReal_nonneg (intenseP P K G F.lip))
omit Z F in
lemma billingC (u d a:ℝ):markup P K G u d a≠⊤:=by unfold markup; finiteness

lemma effects : ∃ Q:Layer (Long G.ColorIndex) (Long G.ColorIndex), Albedo (blockQ G P.L) (blockQ G P.L) Q ∧ chestE (blockQ G P.L) (blockQ G P.L) (widthK P K G σ Ω α) Q (markup P K G σ Ω α) ∧ lap (cousin P K G B) Q=ID _∧lap Q (cousin P K G B)=ID _ :=by
 obtain ⟨c,hc⟩:= arch P K G B F Z
 have hw :trunkCost P K G σ Ω ≠⊤:=by unfold trunkCost;finiteness
 have hp:= width_pos P K G B F
 exact pricingX _ (spliceR P K G B) _ hw (shellsC P K G B F) hc F.pos (intenseP P K G F.lip) (by change _ < gauge_K P K G σ Ω α; unfold widthK at *;linarith) hp

def cable:= (effects P K G B F Z).choose
lemma cafe : Billed (cable P K G B F Z):=(effects P K G B F Z|>.choose_spec.2.1).billed (width_pos P K G B F).le (billingC P K G σ Ω α)
lemma ortho_cable (n):let U:= blockQ G P.L
                      let P':= ledgerRow U U (cable P K G B F Z) n; let Q':= ledgerRow U U (cousin P K G B) n
                      Q'*P'=1∧P'*Q'=1:=by
 intro U P' Q'
 have hz:= (effects P K G B F Z).choose_spec
 have he:Billed (cousin P K G B):=(shellsC P K G B F).billed F.pos.le (by unfold trunkCost;finiteness)
 have ht:= cafe P K G B F Z
 exact ⟨(Ledger.lap U U U n he ht hz.1).symm.trans (by rw [cable,hz.2.2.1,main_zero]),(Ledger.lap U U U n ht he (spliceR P K G B)).symm.trans (by rw [cable,hz.2.2.2,main_zero])⟩
end YM.RegulatorIR.Oracle
