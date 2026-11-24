import YM.OPE.Loom.Ruling
import YM.OPE.Script.Arrival
/-! # Financing utilities of Patrol
- One common simple scheduled path. All demands eventually ready. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{n: Side} {C:Family G} {k j:ℕ} {a : ℝ}
variable {W r D}{σ χ:ℕ→ℝ} {b K:ℕ}
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "Γ" => C.path.levels.budget
local notation "Q" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
variable (h:Sharper C W r D)
-- all low steps in our bodies after root threshold far; eventually operations at ANY horizon
structure Tune (C:Family G) (W:Bid.Worth)(r:ℕ→ℕ)(D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) (σ χ:ℕ→ℝ) : Prop where
    cuts : Sharper C W r D
    tune : G.Simple
    seed : C.Makes
    thor : ManyCopies.Thor C.path (renal C.path.levels) r D σ χ (C.ref 0)
    sworn : SwornClusterCuts C (μ:=D) («δ»:=renal C.path.levels) (r:=r) (C.ref 0) 0 χ (renal C.path.levels) (fun i=>C.path.levels.clock.hatBeta (i+1))
include h

lemma enroll (hk:C.Makes) (hx:G.Simple): ∃ σ χ,Tune C W r D σ χ:=by obtain ⟨χ,hχ⟩:= Loom.secret h; obtain ⟨σ,hσ⟩:=(hχ 0).city; exact ⟨σ,χ,h,hx,hk,hσ,hχ _⟩
namespace Tune
omit h
variable {h}(E:Tune C W r D σ χ)
include E
lemma brine (i:ℕ): Brine C.path i δ η:=⟨fun i _=> E.cuts.system.costs.stay.water _ (Nat.zero_le i),fun i _=> E.cuts.system.costs.stay.mint _ (Nat.zero_le i),fun i _=> E.cuts.system.costs.stay.split _ (Nat.zero_le i),fun i _=> E.cuts.system.costs.stay.support _ (Nat.zero_le i)⟩
lemma mantle (hk:C.ref 0 ≤ k) : ClusterPars C.path δ χ r k:=⟨E.sworn.crisp _ hk,E.sworn.funs _ hk,E.sworn.bars _ hk⟩
lemma strong (hk:C.ref 0 < k){N p:ℕ}(hx:k≤N): MergeProof.Menu.Arsenal (C.path.rep N p k):=by
   cases k with
   | zero=> omega
   | succ j=> exact (E.thor.moon N p j (by omega) hx).1.contact
lemma protectors (w:ℝ)(hw:0<w)(i j:ℕ): 0<stair (near C.path.levels) w i j := by
    -- includes m<sanc easy
    induction j with
    | zero=>exact hw
    | succ j IH=> by_cases hi:i ≤ j
                  · exact (by unfold stair; rw [march,if_pos hi]; exact mul_pos ((E.brine i).water _ hi|>.1) IH)
                  unfold stair; rw [march,if_neg hi]; exact hw
lemma stair_factor (i:ℕ) {m n:ℕ}(h:m < n){a:ℝ}(hp:i ≤ m)(he:0<a): stair η a i n ≤ stair η a i m:= by
   have he : AntitoneOn (stair η a i) (Set.Ici i):= by
      intro x hx y hy he'; induction y,he' using Nat.le_induction with
      | base=>rfl
      | succ y hz IH=>
         have hg : i ≤ y:= le_trans (show i ≤ x from hx) hz
         refine le_trans ?_ (IH hg); unfold stair; rw [march,if_pos hg]; exact mul_le_of_le_one_left (E.protectors _ he _ _|>.le) ((inv_le_one₀ (by exact zero_lt_one.trans ((T).fits.delayed (y+1)))).2 ((T).fits.delayed _|>.le)) -- helper
   exact he hp (hp.trans h.le) h.le
lemma anchor_march (hp:0<a) : stair η a k k=a:= by unfold stair; rw [marines k η _ (fun _=>hp)];
lemma fall_march (hp:k ≤ j): stair η a k (j+1)=η j*stair η a k j:= by unfold stair; rw [march,if_pos hp];
omit E in
lemma stride_exit : 1≤η k*δ k*Real.exp ((Loom.count C 100 k:ℝ)/24):=by
    let t:= (Q) (k+1); have ht: 1<t:= ((T).fits.delayed _); have hz:0 < Real.log t := Real.log_pos ht
    let q:=(Loom.count C 100 k:ℝ); have hx: (100:ℝ)* Real.log t ≤ q:= by exact_mod_cast (Nat.le_ceil ((100:ℝ)* Real.log t)); -- over
    change 1≤t⁻¹*t^(-(2:ℝ))*Real.exp _; have hf:= show 0<t from zero_lt_one.trans ht; rw [Real.rpow_neg hf.le, ← mul_inv_rev,← div_eq_inv_mul,Real.rpow_two,← pow_succ,one_le_div (by positivity)]
    apply le_trans _ (Real.exp_monotone (by linarith only [hz,hx] : 3*Real.log t ≤ q/24)); rw [show (3:ℝ)=(↑(3:ℕ):ℝ) from rfl,Real.exp_nat_mul,Real.exp_log hf] -- Pow native
variable {I:Type}[Fintype I][DecidableEq I] {x y:I→ℝ} {B:Census I} {o:I→Site n}
lemma pebbles (hp:∀ i:ℕ,i=k→∀ j,η i*y j ≤ x j)(hq:∀ i,0<x i)(hx:∀ i,0<y i)
    (he:∀ i j,i≠j→ Loom.stride C 100 k-4 ≤ separation (o i) (o j)) : Repegs o (Γ k).B (fun i=>δ k*x i) y (1/2) 1 B:=by
    have hδ:0 < δ k:= (E.brine k).water _ le_rfl|>.2; have hη:0 < η k:= (E.brine k).water _ le_rfl|>.1
    refine Loom.buys (p:=Loom.count C 100 k) (by intro s h i ha b hb hh; simpa [Loom.stride] using he i b hh) ((Γ k).B_pos) (Loom.count_pos (by norm_num)) hx (fun i=>mul_pos hδ (hq i)) ?_
    intro i; let t:=Real.exp ((Loom.count C 100 k:ℝ)/24); have ht:1≤η k*δ k*t:= stride_exit; have hw:= mul_le_mul_of_nonneg_left (hp k rfl i) (show 0 ≤ δ k*t by have hx:0 ≤ t:=(Real.exp_nonneg _); positivity); have hz:= hx i; refine le_trans (le_mul_of_one_le_left hz.le ht) (le_trans (le_of_eq ?_) (hw.trans_eq ?_)) <;> unfold t <;>ring
lemma fog_mono (d:ℕ) {m k:ℕ}(hk:m≤k) : 0<ζ d k ∧ ζ d k ≤ ζ d m ∧ ζ d m ≤ 1 := by
    have hb i:1<Q i:= (T).fits.delayed _; have hx i:0<Q i:= zero_lt_one.trans (hb i); have hQ: Monotone Q:= fun a b h=> add_le_add_right (mul_le_mul_of_nonneg_left ((YM.OPE.scale_mono C.S).monotone h) (Gauge.slopeConstant_pos E.tune).le) _
    let c:=MergeProof.winter G d
    unfold fly fog; refine ⟨inv_pos.mpr (pow_pos (hx _) _),(inv_anti₀ (pow_pos (hx _) _) (pow_le_pow_left₀ (hx m|>.le) (hQ hk) _)),?_⟩; rw [inv_le_one₀ (pow_pos (hx _) _)]; exact one_le_pow₀ (hb _|>.le)
end Tune
end YM.OPE.Yarn
