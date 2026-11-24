import YM.RegulatorIR.Oracle.Bolts

/-! Build Φ from the transported Tree representative. Compare D0 to
restored fields, in counting basis. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G:Gauge}{n p: Side} {L:Side} {α σ:ℝ}(P:Patch)(H:KernelChoices)
-- witness J (not inversion-aligned yet)
def adult (R:Cross P.L (TypeFace 1) (TypeFace 1))(G:Gauge) : Bloch.Row (Co P.L (PAC G 1)) (PAC G 1):=fun i j z=>if i.2.2=j.2 then R (i.1,i.2.1) j.1 z else 0
def ruling (G: Gauge) (R:Cross P.L (TypeFace 1) (TypeFace 1)) := lading (blockQ G P.L) (linksQ G) (adult P R G)
variable (R: Cross P.L (TypeFace 1) (TypeFace 1)) (G n)
lemma seatV : ledgerRow (blockQ G P.L) (linksQ G) (ruling P G R) n=tensor G (installed (tileB P.L n) R) :=by
 unfold ruling; rw [ledger_lade]; ext1 i j
 rcases i with ⟨x,y,w⟩;rcases j with ⟨a,b,u⟩
 unfold FreeResolvent.tensor installed;rw [Matrix.submatrix_apply]; change (adult P R G).acts n (splitCo (tileB P.L n) (PAC G 1) _) (a,b,u)= _; simp_rw [split_co]; rw [Matrix.of_apply]; split
 next h=> simp_rw [Row.acts,Matrix.of_apply, adult,if_pos h]; rw [Matrix.submatrix_apply,split_co];rfl
 next h=> unfold Row.acts; rw [Matrix.of_apply]; simp_rw [adult]; simp [h]
lemma adult_price (h:R.strip σ α)(he:0≤α): (adult P R G).strip σ α:=by intro i j;unfold adult; split;exact h _ _; simp [Laurent.Width, RG.SumBudget,he]
-- build Phi
abbrev gardens (P:Patch)(G:Gauge):= geological P.L G.ColorIndex
variable {G n}
def supportQ (P:Patch)(H:KernelChoices)(n:Side) (x:RegulatorIR.Gain.Point G): Long G.ColorIndex →₀ ℝ:=
 let S:=avenue P H n;let y:=x.1;let k:=x.2
 anchorK S (rentW P.L y) k - spineK k y ((stemF P n).hike (wrap (n*P.L) y))
def activeL (P:Patch)(H:KernelChoices)(G:Gauge):Layer (RegulatorIR.Gain.Point G) (Long G.ColorIndex):= finer (supportQ P H 1)
lemma support_near (p n:Side)(x:RegulatorIR.Gain.Point G) : supportQ P H p x=supportQ P H n x:=by unfold supportQ;dsimp only; rw [walks P n];rfl
lemma activeW : Albedo (gardens P G) (blockQ G P.L) (activeL P H G):=by
 intro x y d;rw [strut,c_shift]
 unfold activeL finer supportQ; dsimp only; rw [Finsupp.sub_apply,Finsupp.sub_apply,rent_add,paths_cs]; exact congr_arg₂ (·-·) (anchored (avenue P H 1) _ _ _ _) (spinal_move ..)
lemma moneyU(σ:ℝ): FundE (gardens P G) (blockQ G P.L) σ (activeL P H G):= FundE.bill_s (activeW P H) (fun i=>(supportQ P H 1 i).hasFiniteSupport) σ
lemma paid_v (g: FreeResolvent.Vec G (n*P.L) 1)(x):(ledgerRow (gardens P G) (blockQ G P.L) (activeL P H G) n*ᵥ g) ((gardens P G).swrap n x)=
 let s:=wrap (n*P.L) x.1;let S:=avenue P H n; let i:=x.2;let U:=component g i;(fixRoot S*ᵥ U) (S.ratio.parent s,vac)- integralLink s ((stemF P n).hike s) U:=by
 dsimp only
 rw [activeL, cargo_of _ (gardens P G) (blockQ G P.L) x n (supportQ P H 1) (activeW P H),support_near P H 1 n,supportQ, show (blockQ G P.L).swrap n= (linksQ G).swrap (n*P.L) from funext fun i=>v_same i ..];rw [_root_.map_sub,revenue,fees_t, ← wageS P.L]
 rfl
def phiQ (G:Gauge) :RegulatorIR.Gain.Bride G:= lap (activeL P H G) (ruling P G R)
def projectionQ (G: Gauge) := RegulatorIR.Gain.valve (ruling P G R) (phiQ P H R G)
lemma albedoX (G:Gauge) : Albedo (blockQ G P.L) (linksQ G) (ruling P G R):= ladingW _ _ _
lemma albedoQ (G:Gauge) : Albedo (gardens P G) (linksQ G) (phiQ P H R G):= (activeW P H).lap (albedoX P R G)
-- assignment eta tracking done later from e, solver receipts. supply pre cost EXACT $h$ to constructor.
lemma phiE (G:Gauge)(h:R.strip σ α)(hp:0≤σ)(hh:0≤α) : FundE (gardens P G) (linksQ G) σ (phiQ P H R G):= FundE.forw (moneyU P H _) (fond _ _ _ (adult_price G P R h hh)) hp
lemma representative (G:Gauge)(h:R.strip σ α)(hp:0≤σ)(hh:0≤α)(x:Vec G n 1)(p):(ledgerRow (gardens P G) (linksQ G) (phiQ P H R G) n*ᵥ x) ((gardens P G).swrap n p)=
   let V:=installed (tileB P.L n) R;
   -( Precision.straighten (avenue P H n) (stemF P n) V *ᵥ component x p.2) (wrap (n*P.L) p.1,vac) :=by
 dsimp only; rw [phiQ, Ledger.lap _ (blockQ G P.L) _ n _ _ (albedoX P R G)]
 · rw [←Matrix.mulVec_mulVec,paid_v, seatV];dsimp only;rw [FreeResolvent.component_mul,Precision.books]; abel
 · exact ((moneyU P H 0).buys le_rfl).1
 · exact ((fond _ _ _ (adult_price G P R h hh)).buys hp).1
end YM.RegulatorIR.Oracle
