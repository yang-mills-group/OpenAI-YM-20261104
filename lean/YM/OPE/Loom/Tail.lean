import YM.OPE.Loom.Bridge
import YM.OPE.Prices.Space
/-!
# Final length calculations for assembly gates on this inquiry
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid ManyCopies PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker Extra.Multi
variable {G:Gauge} {C:Family G}{W r D}(A : Sharper C W r D)
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "P" => C.path.levels.budget
local notation "S" => C.S
set_option quotPrecheck false
variable (t:ℕ)(hG:G.Simple)
include A
include hG in
lemma light : ∀ᶠ i:ℕ in atTop,stride C 50 i-4 ≤ (P i).B^2:=by
   have he(k):1 < X k := (Y).fits.delayed _; let w i:= Real.log (X i)
   have hw:Tendsto w atTop atTop:= Real.tendsto_log_atTop.comp (exists_hat C hG)
   filter_upwards [(hw.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 200] with i hi
   unfold stride; rw [Nat.add_sub_cancel,pow_two]; apply Nat.mul_le_mul_left; suffices H:(count C 50 i:ℝ)+2 ≤ (((P i).B:ℕ):ℝ) by exact_mod_cast H
   let a := w (i+1); have h:200 ≤ a:= hi; have ht:(count C 50 i:ℝ) ≤ 50*a+1:=by simpa only [Nat.cast_ofNat] using! count_le
   let f:ℕ:= (P i).B; let g:ℕ:= (P (i+1)).B; have hf:a^2 ≤ (g:ℝ):= Nat.le_ceil _
   have hg: (g:ℝ)^2 ≤ 2*(f:ℝ)^2:= by exact_mod_cast A.tabs.grows i
   have hv: (g:ℝ) ≤ 2*(f:ℝ):= by nlinarith [pow_le_pow_left₀ (show 0 ≤ (f:ℝ) by positivity) (show (f:ℝ) ≤ (2:ℝ)*f by simp [two_mul]) 2]
   nlinarith only [hv,h,ht,hf]
omit A in
lemma sail (m : ℕ) : ∀ᶠ i:ℕ in atTop, ∀ p,∀ hm:m ≤ i, (C.path.levels.budget i).B^2+1+2*(t*Loom.stride C 50 i+1) ≤ (C.S.toDepth hm p).count.val := by
   let c := C.S.scale; have hc := C.S.divergent; let y i:= (P i).B^2+1+2*(t*stride C 50 i+1)
   have hx: Cheap atTop c (fun i=>(y i:ℝ)):= by
      let k:= fun i:ℕ=>i; have hp:Height C.S atTop c k 1 := first_price; unfold y; push_cast; refine Bill.add (Cheap.power (covers_p hc hp|>.up) hc 2|>.add (Bill.const (1:ℝ) hc) hc) (Cheap.mul (Bill.const (2:ℝ) hc) ?_) hc
      exact Bill.add (Cheap.mul (Bill.const _ hc) (stride_cost hc hp 50|>.up)) (Bill.const 1 hc) hc
   have hg: RateLE atTop c (fun i=>(y i:ℝ)) 0:= rapid hc hx (RateLE.const 1 hc)
   have hh:= hg.mul (first_price.mesh.pays hc : RateLE atTop c (S).a _)
   filter_upwards [(RateIs.const hc (C.S.a_pos m)).outweigh hh (by norm_num) hc] with i hi p hm; let Z:= (C.S.toDepth hm p); rw [← C.S.embeds_scale Z] at hi
   have H : (y i:ℝ) ≤ Z.count.val:= le_of_mul_le_mul_right (by rw [mul_comm ((Z.count.val:ℕ):ℝ)]; exact (Real.le_norm_self _).trans hi) (C.S.a_pos i); exact_mod_cast H
variable {I:Type*} {α : Type}[Fintype α] {a c T u : I→ℝ} {φ : Filter I} {k j : I→ℕ} {v b : ℝ}
include hG
lemma gates (α:Type)[Fintype α] (ha:Tendsto a φ (𝓝[>]0)) (hk: k=(fun i=> arch 50 C (a i)-1))(u:ℕ) (hh:∀ᶠ i in φ,broad C 50 (j i)<a i) : ∀ᶠ i in φ,u≤ k i ∧ Gate (α:=α) C r t (k i) (j i) u (a i):=by
   let m i:= arch 50 C (a i)
   have hm:Tendsto m φ atTop:= arch_growth _ _ ha
   have hz:∀ᶠ i in φ, k i+1=m i:= (hm.eventually_ge_atTop 1).mono fun i hi=>hk.symm ▸ (Nat.sub_add_cancel hi)
   have hB (p:ℕ→Prop)(h:∀ᶠ i in atTop,p i) : ∀ᶠ i in φ, ∀ v ≥ m i,p v:= by obtain ⟨k,h⟩:= eventually_atTop.mp h; exact (hm.eventually_ge_atTop k).mono fun _ hi j hj=>h j (hi.trans hj)
   filter_upwards [ha.eventually (Ioc_mem_nhdsGT ((C.S.a_pos 0).trans_le (gate_b (C:=C) 50 _))),hz,hB _ (light A hG),hm.eventually (sail (C:=C) t u),hm.eventually_gt_atTop u,hB _ (A.limit_r.eventually_ge_atTop (Fintype.card α)),hh] with i ha hz hs hu hU hr hh
   change m i>u at hU; refine ⟨by omega,ha.1,hz.symm ▸ (arch_fails 50 ha.1 ha.2),fun j hj _=>(before 50 ha.1 (v:=a i) (show m i < j from hz ▸ hj)),hh,hz.symm ▸ hr,hz.symm ▸ hs,hz.symm ▸ hu⟩ -- trans rewrites
omit A hG in
lemma fits (R:ℕ) (i:ℕ): ∀ᶠ m:ℕ in atTop, GridApprox.room C.path.levels i m R:= by
   -- note engineering of step and use rate with fixed label.
   let S0:=C.S; let y k:= (S0.scale k); have he: Height C.S atTop S0.scale id 1:=first_price; have hh:= S0.divergent; -- height function for fixed i not tendsto!
   have hx:= ((RateIs.const (c:=30) hh (by norm_num)).mul he.mesh).mul (height0 (note_reg (Y)) he)
   have hz:= (RateLE.const (2:ℝ) hh).mul ((RateLE.mul (he.mesh.pays hh) (RateLE.const (R:ℝ) hh)).add (hx.pays hh|>.mono (by linarith only)) hh)
   exact (RateIs.const hh (C.S.a_pos i)).overtakes hz hh (by norm_num)
end YM.OPE.Loom
