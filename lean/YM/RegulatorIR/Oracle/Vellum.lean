import YM.RegulatorIR.Oracle.Arrange

/-! R1 Supplies postscript. Precost and posterior shell & line. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Step YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping Uniform
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {X:Type} {M:X→ℕ} {n:Page M→Side} {K:KernelChoices} {k p:ℕ}
namespace Circuit
variable (S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G) (t:Page M→Binding.Scale)
local notation "A"=>S.dialect Y G Z t
local notation "T"=>S.lane Y G Z t
-- Sector Meter. Scope at q order & spins momentum k; B.Struct conventions

def leadA (k:ℕ)(i:Flap M) := pack_c G k (Y.receipt.α (S.J i.prev)) (Y.receipt.Ω (S.J i.prev))* ENNReal.ofReal (( (S.sizeL i).val:ℝ)⁻¹)
variable (P:Meter X)
structure Credit (k p:ℕ):Prop where
 levels : Uniform.Poly P fun i=> (M i:ℝ≥0∞)
 allows i: leadA S Y G k i ≤1
 layout : Uniform.Poly (flapL M P) fun i=> tariffJ (S.pactP i) K G (Y.receipt.Ω (S.J i.prev)) (Y.receipt.α (S.J i.prev)) k
 projection : Uniform.Poly (flapL M P) fun i=> post_C (S.pactP i) K G (Y.receipt.Ω (S.J i.prev)) (Y.receipt.α (S.J i.prev)) k
 rayS :Uniform.Poly (flapL M P) fun i=>heatPost (S.pactP i) K G (Y.receipt.Ω (S.J i.prev)) (Y.receipt.α (S.J i.prev)) (Y.receipt.η (S.J i.prev)) k
 clockV i : i≤ p→ Uniform.Poly (flapL M P) fun x=>‖biases (t x.prev) i‖ₑ
 wall i j:i≤p→j≤ i+2→ Uniform.Poly (flapL M P) fun w=> archive (S.pactP w) K G (Z _) i j k
include S Y Z P t
omit S Y Z P t in
private lemma imprint {K:KernelChoices}{n f: Side}{L:Patch}{R: Cross L.L (TypeFace 1) (TypeFace 1)} {s l:ℝ}(h:Even n.val) (ht:l*n.val=s)(hp:f=n*L.L): Gain.Rune (Carto G l s h ht) f (conveyer L K G R):= hp ▸ pipes L K G R h ht
omit S Y P Z t in
private lemma engrave {n f:Side}{P:Patch}{R:Cross P.L (TypeFace 1) (TypeFace 1)}{l s t:ℝ}(h:Even n.val)(hv:Even f.val)(hs:s*f.val=t)(hc:l*n.val=t)(he:f=n*P.L):Layer.Sym (Carto G s t hv hs) (Carto G l t h hc) (starrier P G R):=by
 subst f; exact gears_C P G hv hs h hc (albe_U P G R) (inv_L P G R)
variable (H: Credit S Y G Z t P k p)
include H
lemma payingB : Azur T (S.pushP Y G) (S.takeP Y G) k P (leadA S Y G k):=by
 refine { run:=fun _=>rfl,depth:=H.levels,caps:=H.allows, carryI:=?_, drift:=?_, carryP:=?_,prepaid:=?_,other:=⟨_,H.layout,?_⟩ }
 -- order drift before carry?
 case refine_2=>
   intro i; exact engrave G (S.dual i.next) (S.dual i.prev) (S.comet i.prev) (S.comet i.next) (R:=S.tells Y i) (P:=S.pactP i) (S.seats i)
 case refine_1=>
   intro i; have hp:= S.honored Y i.prev; have he:= S.honored Y i.next; exact sets (S.pactP i) K _ _ G (S.tells Y i) hp.card he.card (S.predicted Y i) (Z _) (fun t=>hp.symmetryP t G)
 · intro i; exact imprint G (S.dual i.next) (S.comet i.next) (S.seats i)
 · intro i; have h:= S.l_p i.prev; have hp:=S.honored Y i.prev; exact pre_slot G (S.pactP i) _ h (S.width_s i) (S.l_p i.next) hp.card.pos (S.predicted Y i).rows hp.card.paid
 intro i; have a:=S.pactP i; have hp:=S.honored Y i.prev; exact turns_row (S.pactP i) K G (R:=S.tells Y i) (S.predicted Y i).rows hp.card.paid hp.card.pos (S.l_p i.prev) (S.width_s i) (S.l_p i.next)
end Circuit
end YM.RegulatorIR.Oracle
