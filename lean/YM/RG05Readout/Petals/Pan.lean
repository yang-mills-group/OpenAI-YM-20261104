import YM.RG05Readout.Petals.Tight
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}
/-!
# Manifest erasures under multi-charge. Price semantics additive.
 General vectors x only dollar (CAN grow) paid via normalization first in next file. Need actual valuation for residual discrepancy: witness is genuine Stencil bought on SAME extraction, not field projected by FREE. Supports price works before any normalization inside correlation tests. -/
open Dash Extraction Extraction.Lease UVExt -- Avoid `Slots` ambiguity namespace Petals.Slots
/-!
# Detector add-ons for reaching U.Spans on common ordered extraction
-/
open Kernel Bay
local notation "T'"=> C.S.a
local notation "t₀"=> C.S.a N
local notation "Z"=> C.side N p
section
variable (L':Poem C b) (x:Leafage C d)
local notation "I"=> Fin L'.n
local notation "K"=> Fin (L'.n+1)
variable (P:Extraction.Lease.Trial C)
local notation "F"=> C.O N p
local notation "r"=> L'.opening
abbrev specimen (g:Body)(P: Extraction.Lease.Trial C)(N p:ℕ): Goods G (C.side N p):=(C.S.a N:ℂ)^4 • ∑ i:Site (C.side N p), g.val (C.S.place i) • P N p i
local notation "x'"=> specimen L'.opening P N p
lemma marked (hP:∀ z,Continuous (P N p z)): Bid.targetB P L'.sight N p=preamble L' N p x':=by
    let t:= L'.token; let r'(z:I→Site Z)(v):=∏ i:I, C.seen (t i) (z i) v; let a(y:Site Z):= L'.opening.val (C.S.place y); let b(z:I→Site Z):=∏ i:I,(L'.post i).val (C.S.place (z i)); let E':= Fin.consEquiv (fun _ :Fin (L'.n+1)=> Site Z)
    have hp(z:I→Site Z):Continuous (r' z):= continuous_finsetProd _ fun i _=>C.continuousO ..
    have hc(z:I→Site Z)(y:Site Z) : featuring P L'.sight.left L'.sight.i N p (Fin.cons y z)= column L' N p z (P N p y):=by
       unfold featuring Bay.column; congr 1; funext u; dsimp only [Poem.sight]; change (∏ i: Fin (L'.n+1),_)= _; rw [Fin.prod_univ_succ, if_pos rfl]; congr 1
    have hd(z:I→Site Z)(u:Site Z):L'.sight.f (Order.cells C N p (Fin.cons u z))= a u * b z:= L'.splits .. -- dependent
    have ht (z:I→ Site Z): column L' N p z x' = (t₀:ℂ)^4 * ∑ y:Site Z,a y*column L' N p z (P N p y):=by
       unfold specimen; let μ:= law G Z (C.beta N p)
       let f(y:Site Z):=fun v=> a y*(P N p y v*r' z v)
       have hi(y):Integrable (f y) μ:= continuous_integrable _ (((hP y).mul (hp z)).const_mul _)
       rw [Bay.column]; unfold moment; simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul, mul_assoc, Finset.sum_mul, integral_const_mul]; rw [integral_finsetSum _ (fun i (_:i∈(Finset.univ : Finset (Site Z)))=> hi i)]; apply congr_arg; simp_rw [Bay.column,moment,← integral_const_mul]; rfl
    unfold Bid.targetB Bay.preamble; rw [show 4*L'.sight.n=4*L'.n+4 from by change 4*(L'.n+1)=_;omega,pow_add,mul_assoc]; congr 1; change _ * (∑ x:(Fin (L'.n+1)→Site Z),_) =_; rw [←Equiv.sum_comp E',Fintype.sum_prod_type, Finset.sum_comm]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; rw [ht]; change _= b z*((t₀:ℂ)^4*_); rw [mul_left_comm (b z) ((t₀:ℂ)^4),Finset.mul_sum (a:=b z)]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; exact (congr_arg₂ (HMul.hMul) (hd z i) (hc z i)).trans (by ring)

-- Preamble continuity order.Lift
lemma onward_minus (g q: Goods G (C.side N p)) (hG: Continuous g)(hq:Continuous q): preamble L' N p (g-q)=preamble L' N p g-preamble L' N p q:=by
   unfold preamble; rw [← mul_sub, ← Finset.sum_sub_distrib]; congr 1; apply Finset.sum_congr rfl; intro z _; rw [←mul_sub]; congr 1; let u(v):= ∏ i:I,C.seen (L'.token i) (z i) v; have hu:Continuous u:= continuous_finsetProd _ fun i _=> C.continuousO ..; unfold Bay.column moment; simp_rw [Pi.sub_apply,sub_mul]; exact integral_sub (continuous_integrable _ (hG.mul hu)) (continuous_integrable _ (hq.mul hu))

--- Campaign denominator at Poem.Lambda uses stock caps for C.seen.C_P
local notation "d₁"=> ∑ i:I,(L'.token i).1
include h
variable (hG:G.Simple)
include hG
lemma loose : ∃ b':Cutoffs→ℝ,(∀ i,0≤ b' i)∧ Slow C f b'∧ ∀ᶠ i in f.fuse,∀ (B:ℝ)(x:Config G (C.side i.1 i.2)→ℂ), Continuous x→ (∀ v,‖x v‖ ≤B) → ‖preamble L' i.1 i.2 x‖ ≤ b' i*B*((C.S.a i.1)^d₁)⁻¹:=by
   choose c hc hC hP using fun i:I=> stays (RawProtected.visits (f:=f) h hG (show C.label (L'.token i).1 from (L'.token i).2) le_rfl)
   let p'(i:Cutoffs):=(Extraction.length C.S i.2)^(4*Fintype.card I); have hh:Slow C f p':=by intro ε h'; rw [Order.fused,Order.late]; refine Eventually.of_forall fun v=> ?_; unfold p'; exact (show Tendsto (fun N=> Real.exp (ε*C.S.scale (f.mesh N))) atTop atTop from Real.tendsto_exp_atTop.comp ((C.S.divergent.comp f.mesh.cofinal).const_mul_atTop h')).eventually_ge_atTop ‖p' (0,f.per v)‖
   refine ⟨_,fun i=> mul_nonneg (show 0≤ p' i by unfold p' Extraction.length; positivity) (Finset.prod_nonneg (s:=Finset.univ) (f:=fun j=>c j i) fun j _=>hc j i),hh.mul (productC hC Finset.univ),?_⟩
   filter_upwards [eventually_all.mpr hP] with i hi B x hX hQ; obtain ⟨N,p⟩:= i
   have hB:0≤B:=(norm_nonneg _).trans (hQ (fun _ => 1)); let P:=(N,p); let A:= ∏ j:I,c j P
   let z:=(∏ j:I,c j P*((C.S.a N)^((L'.token j).1))⁻¹); have he:z=A*(C.S.a N^d₁)⁻¹:=by unfold z; rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,Finset.prod_pow_eq_pow_sum]
   let Y(z:I→Site (C.side N p)):= (∏ i:I,(L'.post i).val (C.S.place (z i)))*column L' N p z x
   have he' (z':I→ Site (C.side N p)) : ‖Y z'‖ ≤ B*z:=by
       apply (norm_mul_le ..).trans; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_); rotate_left
       · rw [norm_prod]; apply Finset.prod_le_one (fun _ _=> norm_nonneg _); intro j _; let u:= L'.singer j.succ; let z:= C.S.place (z' j); change ‖(↑(u z):ℂ)‖≤1; rw [Complex.norm_real,Real.norm_of_nonneg u.nonneg]; exact u.le_one
       let f₁(v):=∏ i:I,C.seen (L'.token i) (z' i) v; have hf:Continuous f₁:=continuous_finsetProd _ (fun i _=> C.continuousO ..)
       have hu:∀ v, ‖x v*f₁ v‖≤B*z:=fun v=> (norm_mul_le ..).trans (mul_le_mul (hQ _) (by unfold f₁; rw [norm_prod]; apply Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>hi i _ v)) (norm_nonneg _) hB); change ‖∫ U,x U*f₁ U∂law G _ _‖ ≤_; exact (norm_integral_le_of_norm_le_const (μ:=law G (C.side N p) (C.beta N p)) (Eventually.of_forall (p:=fun v=>‖x v*f₁ v‖ ≤ B*z) hu)).trans_eq (by simp)
   apply le_trans (b:= (Extraction.length C.S p) ^ (4*Fintype.card I)*(B*z)); apply le_trans _ (amount Y (B*z) he'); unfold preamble; simp only [Finset.prod_const, Finset.card_univ, ← pow_mul,Fintype.card_fin]; rfl -- change 
   rw [he]; apply le_of_eq; unfold A p'; dsimp only [P]; ring
end
end YM.RG05Readout.Petals
