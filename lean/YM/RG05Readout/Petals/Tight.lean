import YM.RG05Readout.Petals.Absorb
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
namespace Kernel
open UVExt.Slots
open Bay
/-! Detector absorb (actual stencil). No hidden inverse assumption. Only
 finite detector positive estimates on T; Base.SHARP and Clean. Keeps a bounded
 family on same tickets to be transported to simultaneous joint moments. -/
variable {T S:YM.Table C.book}{R:Dash.Bin S}{E:DiffPlan T}{L0:ℕ→YM.Table C.book}{I:Type}[Fintype I]{m:ℕ} {v:Cutoffs→C.label d}(H:Next.Extract.Base C f S L0 R T E) {D₀:I→Poem C m}
variable {P:Trial C}{c:ℝ}
-- cutoff binder
include h H
lemma Banking (hQ: Proctor C f R m d I D₀ c)(hp: StrongBin C R f d)(hw: vet C f d P)(ht: Stencilled f P)
    (hc:∀ i:I,∃ A:ℝ, ∀ᶠ u:ℕ×ℕ in f.fuse, ‖Bid.targetB P (D₀ i).sight u.1 u.2‖≤A): ∃ x:Rowe C d, (∀ i,(R d).step i (x i)=x i)∧ Reveals C f P x:=by
    obtain ⟨z,hz,hP⟩:=hw; let x:Rowe C d:= fun i=> (R d).step i (z i); let a(i):=1+‖x i‖; let s (i:Cutoffs):ℂ:= (↑((a i)⁻¹):ℂ); let W:= fun i=> s i • x i
    have he:Reveals C f (times s P) W:= stretched h hp ht z hz hP -- cast
    let X(i:I):=snapshots (D₀ i).sight d; let η (i :Cutoffs) (j:I):ℂ:= targetB (times s P) (D₀ j).sight i.1 i.2-X j i (W i)
    have hC : Tendsto (fun u:Cutoffs=> ∑ j:I,‖η u j‖) f.fuse (𝓝 0):=by
       suffices hh:Tendsto (fun u:Cutoffs=> ∑ j:I,‖η u j‖) f.fuse (𝓝 (∑ _j:I,‖(0:ℂ)‖)) from by simpa only [norm_zero,Finset.sum_const_zero] using hh
       exact tendsto_finsetSum Finset.univ fun i _=> (on_profile h W _ he H.center).norm -- namespace?
    have hw(i): (R d).step i (x i)=x i:= (R d).projection ..; refine ⟨x,hw,produce h hp z hz ht hP ?_⟩; change tight C f x
    choose A hA using hc
    let K:=∑ i:I,A i; have hc:0<c:=hQ.pos
    refine ⟨2*K/c+1,?_⟩; refine (Order.fused f (fun j=> ‖x j‖≤2*K/c+1)).mp ?_; filter_upwards [hC.eventually (ge_mem_nhds (half_pos hc)), eventually_all.mpr hA,hQ.detector] with u hu ht hb
    have hv:0< a u:=add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _); let r:= a u
    have he':‖s u‖=r⁻¹:= by unfold s; rw [Complex.norm_real,Real.norm_of_nonneg (inv_pos.mpr hv).le] -- if cast insertion
    have hs: c*‖x u‖ ≤ K+r* ∑ i:I, ‖η u i‖:=by
       have hf(i:I): ‖X i u (x u)‖ ≤ A i + r*‖η u i‖:=by
          let t:= targetB P (D₀ i).sight u.1 u.2; have ht₁ : η u i=s u * (t-X i u (x u)) :=by unfold η W; rw [paid_one (P:=P) .., map_smul,mul_sub]; rfl
          rw [ht₁,norm_mul, he',← mul_assoc, mul_inv_cancel₀ hv.ne',one_mul]; have ht': ‖t‖≤A i:=ht i; rw [norm_sub_rev]; linarith only [norm_sub_norm_le (X i u (x u)) t, ht']
       unfold K; rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact le_trans (hb _ (hw u)) (Finset.sum_le_sum fun i _=> hf i)
    have hh: a u* ∑ i:I,‖η u i‖≤ r*(c/2):= mul_le_mul_of_nonneg_left hu hv.le; apply sub_le_iff_le_add.1; rw [le_div_iff₀ hc]; dsimp only [r,a] at *; linarith only [hh,hs] -- check

-- interpolate results on stands along given fuse. stable between two choices
lemma pilot_similarity (hQ: Proctor C f R m d I D₀ c) {Z:Trial C}(hp:Reveals C f P v) {w:Rowe C d}(ht: Reveals C f Z w)(hv:∀ i,(R d).step i (v i)=v i)(hw:∀ i,(R d).step i (w i)=w i)
   (H0:∀ i:I,Tendsto (fun u:Cutoffs=> targetB P (D₀ i).sight u.1 u.2-targetB Z (D₀ i).sight u.1 u.2) f.fuse (𝓝 0)) : Tendsto (fun u=>v u-w u) f.fuse (𝓝 0):=by
     let F(u):=v u-w u; let X(i:I):=snapshots (D₀ i).sight d
     have he(i:I): Tendsto (fun u=>X i u (F u)) f.fuse (𝓝 0):=by
         have ht':= ((H0 i).sub (on_profile h v ((D₀ i).sight) hp H.center)).add (on_profile h w ((D₀ i).sight) ht H.center); rw [sub_zero,zero_add] at ht'; apply ht'.congr' (Eventually.of_forall fun j=>?_); rw [show F j=v j-w j from rfl,map_sub]; unfold X; abel
     have hr:c≠0:= hQ.pos.ne'; have ht0:= tendsto_finsetSum (Finset.univ: Finset I) (fun i _ => (he i).norm); let s (u:Cutoffs):= (∑ i:I, ‖X i u (F u)‖)/c; have hu:Tendsto s f.fuse (𝓝 0):=by simpa only [norm_zero,Finset.sum_const_zero,zero_div] using ht0.div_const c
     let H0':Tendsto (fun u=> ‖F u‖) f.fuse (𝓝 0):= squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) (hQ.detector.mono fun i hi=> by unfold s; rw [le_div_iff₀ hQ.pos, mul_comm]; exact hi _ (by unfold F; rw [map_sub,hv,hw])) hu
     exact tendsto_zero_iff_norm_tendsto_zero.mpr H0'
end Kernel
end YM.RG05Readout.Petals
