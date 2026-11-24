import YM.OPE.Compatible.Camo.Beam
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
open Stroke Ibis Borealis Borealis.Galea
variable {L:I→Host K T} {V B W S h' A F D ε C' X:I→ℝ} {l:Filter I}{J:I→ℕ} (Y:∀ i,CoT (L i))(x:∀ i,Site (L i).f)
local notation "PΘ"=> fun i=> CoT.hymn (Y i) (W i) (B i)
abbrev Cold (H:Host K T)(Y:CoT H)(i:Bid.Dir G H.c) (w:ℝ):=Y.a (Y.F (represent (w • i)))
-- StageS.W orbit positivity and chars
structure HoodM (H:Host K T)(Y:CoT H)(v:Bid.Dir G H.c)(u s:ℝ):Prop where
         frame :∀ i:Dim Y.x (4* Y.b), G.chord ((represent (u • v)) i.val) ≤ s
         floorY : Belts Y.b*s≤Y.P.B
         tollY : sizeQ Y.b*(Y.T.threshold⁻¹ * (Belts Y.b*s))^2 ≤ Y.P.r^2/2
variable (h:Quench V l C' A B ε W)(hM: RateLE l V X 0)(hz:RateLE l V (fun i=>((Y i).b:ℝ)) 0)(hT:RateLE l V (fun i=> CotV (L i) (Y i) (k+6) (S i) (W i)) 0)
variable (V': I→ℝ)
local notation "N0"=>fun i=> StageS (L i) (x i) (J i) (X i)
local notation "PΦ"=> fun i v=> Qspot (L i) (x i) (J i) v
variable (hp:∀ᶠ i in l,Covered (L i) (Y i).x (Y i).b (x i) (J i)∧(Y i).Note (S i) (k+6)∧0 ≤ V' i∧∀ w∈ StageS (L i) (x i) (J i) (X i), HoodM (L i) (Y i) (Qspot (L i) (x i) (J i) w) (ε i) (V' i))
local notation "αQ"=>-(11/10:ℝ)
include h hz hp hM hT
lemma Ort_S : Large (N0) l V (fun i w=> Cold (L i) (Y i) ((PΦ) i w) (ε i) - (((PΘ) i) w).atK (ε i)) (αQ):=by
         let v (i):= crestPrice G (X i); let vT (i):= CotV (L i) (Y i) (k+6) (S i) (W i); let η(i):= (Y i).b; let Q(i):= RedG G (η i) (v i); let f(j:ℕ)(i):= Mā G j (η i) (v i); let r(i):=(1+‖B i/2‖)*Q i
         have hc:= h.light; have he(t:ℝ):= RateLE.const t hc; have hE := h.fine.pays h.light; have hu:RateLE l V v 0:= ((he _).mul hM).mono (by norm_num)
         have hR: RateLE l V (fun i=> RoadK (η i)) 0:= ((((he 2).mul ((he 4).mul hz)).mono (by norm_num)|>.add (he 2) hc).add (he 1) hc); have hf (i:ℕ): RateLE l V (f i) 0:= (((he (magnol G i)).mul (hR.pow i hc)).mul (((he 1).add hu hc).pow i hc)).mono (by simp); have hQ: RateLE l V Q 0:= (he 1).add (((hf 1).add (hf 2) hc).add (hf 3) hc) hc; have ht: RateLE l V (fun i=> B i/2) 0:=by simpa only [div_eq_mul_inv,add_zero] using h.toll.mul (RateLE.const ((2:ℝ)⁻¹) hc)
         have hv: RateLE l V r 0:= (((he 1).add ht.norm hc).mul hQ).mono (by norm_num); have hs: RateLE l V (fun i=> γX (r i) (ε i)) αQ:= (((he (Nat.factorial 3:ℝ)).mul (((he 3).mul hv).pow 3 hc)).mul (hE.pow 3 hc)).mono (by norm_num)
         have hh: RateLE l V (fun i=> vT i*((‖ratio ε W i‖*((f 4 i)*(ε i)^3)+rebate (B i) (ratio ε W i) (ε i) (Q i))+γX (r i) (ε i))) αQ:= (hT.mul ((((h.Toledo.norm.mul ((hf 4).mul (hE.pow 3 hc))).mono (by norm_num)|>.add (h.billE _ hQ) hc).add hs hc))).mono (by norm_num); refine ⟨_,hh,?_⟩
         filter_upwards [hp,h.fine.pos,h.wide.pos,(h.fine.tends (by norm_num) h.light).eventually (ge_mem_nhds zero_lt_one)] with i hi hI hW hE w hw; obtain ⟨he,hv,ht,hY⟩:=hi; obtain ⟨hf,hL,hH⟩:=hY w hw; let v':= Qspot (L i) (x i) (J i) w; have hx:=μnorm (L:=L i) (Y i).x v' (r:=v i) hw (η i); unfold CoT.hymn Elev; rw [Tess (Y i).T (Y i).F (Y i).a (Y i).x _ _ _ _ he]; apply le_trans _ (Real.le_norm_self _); exact Veil (Y i).x _ _ (W i) _ _ _ hv (B i) v' hW.ne' (V' i) ht _ _ _ hI hE hx.1 hx.2 hf hL hH -- bug order
end
end YM.OPE.Cameo
