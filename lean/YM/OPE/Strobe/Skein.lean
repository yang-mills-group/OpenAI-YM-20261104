import YM.OPE.Strobe.Letter
import YM.OPE.Cluster.Spline
/-! # Spaces for a couple. Width eight deliberately excessive. Port of Arbor/Subpower layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℕ→ℝ} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
variable {o : I→Site (C.side j p)} (h:m ≤ k)
include h
lemma woven_behind (hc:∀ i,8*‖C.S.place (o i)‖≤ C.S.a m) (ht:2*((T|>.budget k).B^8+4) ≤ (C.S.toDepth h p).count.val) : Cross ((T|>.budget k).B^4) ((Z k).place (fun i=> loops C j p (o i) k)):=by
   let R₁:= C.S.toDepth h p; let K:=R₁.count.val; let d:= C.S.a m; let B:=(T|>.budget k).B
   have he(i): 2*separation ((loops C j p) (o i) k) 0 ≤ K-B^8:=by
       have hx:= upper_pair (k:=k) (o i) 0; rw [loops_id,sub_zero] at hx
       let l:=separation ((loops C j p) (o i) k) 0; have hr:d= C.S.a k*(K:ℝ):=(C.S.embeds_scale R₁).symm; have hf: (2:ℝ)*((B:ℝ)^8+4) ≤ K:=by exact_mod_cast ht
       have hz : 2*l + B^8 ≤ K:=by
           apply (Nat.cast_le (α:=ℝ)).mp; push_cast; let a:=C.S.a k; have hy:0<a:= C.S.a_pos k; change a*(l:ℝ)≤a+_ at hx; apply le_of_mul_le_mul_left _ hy; change d=a*K at hr; nlinarith only [hy,hx,mul_le_mul_of_nonneg_left hf hy.le,hr,mul_nonneg hy.le (pow_nonneg (show (0:ℝ)≤B by positivity) 8),(show 8*‖C.S.place (o i)‖≤ d from hc i)]
       unfold l at hz; exact Nat.le_sub_of_add_le hz
   rintro ⟨u,i⟩ ⟨v,l⟩ hu; simp_rw [placeR h]
   let U:= bites C m j p (o i) k (u,true); let Y:=bites C m j p (o l) k (v,true); have h₁:= reachBit C m j p k (o i) h u true; have h₂:= reachBit C m j p k (o l) h v true
   let Za:=Mix.camp C p m k; have hf: K ≤ separation (Za u) (Za v):=by dsimp only [Za]; rw [elev C m p k h u, elev C m p k h v,Station.both]; exact Nat.le_mul_of_pos_right _ (separation_pos _ _ hu)
   have hy:=separation_triangle (Za u) U Y; have hX:= separation_triangle (Za u) Y (Za v); rw [separation_comm (Za u) U] at hy
   change separation U (Za u) ≤ separation ((loops C j p) (o i) k) 0 at h₁; change separation Y (Za v) ≤ separation ((loops C j p) (o l) k) 0 at h₂; change (B^4)^2 ≤ separation U Y; rw [← pow_mul, show 4*(2:ℕ)=8 from rfl]; have h':2*(B^8+4)≤ K:= ht; have hc:=he i; have ht':= he l; omega

omit h
include H
lemma masksEt : ∀ᶠ i:ℕ in atTop,stride C 100 i-4 ≤ ((T).budget i).B^2:= by
   let A:= C.path.levels; let w i:= Real.log (A.clock.hatBeta i); have he k:1<C.path.levels.clock.hatBeta k:= (T).fits.delayed _; have hw:Tendsto w atTop atTop:= Real.tendsto_log_atTop.comp (exists_hat C H.tune)
   filter_upwards [(hw.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop 400] with i hi; let PZ:=A.budget
   unfold stride; rw [Nat.add_sub_cancel,pow_two]; apply Nat.mul_le_mul_left; suffices h:(Loom.count C 100 i:ℝ)+2 ≤ ((PZ i).B:ℝ) by exact_mod_cast h
   let a:=w (i+1); have h:400≤a:=hi; have hx:(Loom.count C 100 i:ℝ) ≤ 100*a+1:=by simpa only [Nat.cast_ofNat] using! Loom.count_le
   let f:ℕ:= (PZ i).B; let g:ℕ:= (PZ (i+1)).B; have hf:a^2 ≤ (g:ℝ):= Nat.le_ceil _; have hg: (g:ℝ)^2 ≤ 2*(f:ℝ)^2:= by exact_mod_cast H.cuts.tabs.grows i
   have hv: (g:ℝ) ≤ 2*(f:ℝ):= by nlinarith [pow_le_pow_left₀ (show 0 ≤ (f:ℝ) by positivity) (show (f:ℝ) ≤ (2:ℝ)*f by simp [two_mul]) 2];
   nlinarith only [hv,h,hx,hf]
omit H in
private lemma sailsEt (m:ℕ) : ∀ᶠ i:ℕ in atTop,∀ p,∀ hm:m ≤ i, 2*((C.path.levels.budget i).B^8+4) ≤ (C.S.toDepth hm p).count.val:=by
   let c:= C.S.scale; have hc:= C.S.divergent; let f i:=2*((C.path.levels.budget i).B^8+4)
   have hv:=Cheap.power (covers_p (C:=C) hc first_price|>.up) hc 8; have hh: Cheap atTop c (fun i=>(f i:ℝ)):= by unfold f; push_cast; exact Cheap.mul (Loom.Bill.const _ hc) (hv.add (Loom.Bill.const _ hc) hc)
   have hp:= RateLE.mul (rapid hc hh (RateLE.const 1 hc)) ((first_price (C:=C)).mesh.pays hc); filter_upwards [(RateIs.const hc (C.S.a_pos m)).outweigh hp (by norm_num) hc] with i hi p hm; rw [← C.S.embeds_scale (C.S.toDepth hm p)] at hi; exact_mod_cast (le_of_mul_le_mul_left ((mul_comm (C.S.a i) (f i:ℝ)).trans_le ((Real.le_norm_self _).trans hi)) (C.S.a_pos i))


local notation "B" => (fun i=>(T|>.budget i).B)
-- s∞ mesh radius comparator, monotonically decreasing
private lemma reducing (i:ℕ) : ((B (i+1))^2+4:ℕ) * C.S.a (i+1) ≤ ((B i)^2+4:ℕ)*C.S.a i := by
   rw [Schedule.a_step]; let w:= (C.S.block i).val; have hw:0<(w:ℝ):= by exact_mod_cast (C.S.block i).pos
   push_cast; rw [←mul_div_assoc]
   apply (div_le_iff₀ hw).mpr; have hx: 2 ≤ (w:ℝ):= by exact_mod_cast (Nat.le_trans (by norm_num:2 ≤ 3) (C.S.block_large i))
   have ht := H.cuts.tabs.grows i; have ht:(B (i+1):ℝ)^2+4 ≤2*((B i:ℝ)^2+4):= by exact_mod_cast (show (B (i+1))^2+4 ≤2*((B i)^2+4) from by change (B (i+1))^2 ≤ 2*(B i)^2 at ht; omega)
   let a:= C.S.a i; let t:= ((B i:ℝ)^2+4)* a; have ht₀:0 ≤ t:= by unfold t; have h:=C.S.a_pos i; unfold a; positivity
   linarith only [mul_le_mul_of_nonneg_right hx ht₀, mul_le_mul_of_nonneg_right ht (C.S.a_pos i).le] -- `w` etc
-- capacity
structure Barrow (C:Family G)(r:ℕ→ℕ)(m n k:ℕ): Prop where
    hbar : m≤ k
    apron i: k ≤ i → stride C 100 i-4 ≤ (C.path.levels.budget i).B^2 ∧ n ≤ r i ∧ ∀ (p:ℕ) (h:m ≤ i), 2*((C.path.levels.budget i).B^8+4) ≤ (C.S.toDepth h p).count.val
lemma rolls (m b:ℕ) : ∀ᶠ k:ℕ in atTop, Barrow C r m b k:=by
   obtain ⟨t,ht⟩:= eventually_atTop.mp ((masksEt H).and ((H.cuts.limit_r.eventually_ge_atTop b).and (sailsEt (C:=C) m)))
   filter_upwards [eventually_ge_atTop m,eventually_ge_atTop t] with i he hx using ⟨he,fun j hj=>ht j (hx.trans hj)⟩
-- beyond.ANY sample at fixed month. arch≥ and failing you need fails and lag; choose hΣ with v≤threshold C 100 0. Then j < k.
lemma bars2 {K:ℕ}{v:ℝ} (A:Barrow C r m K k) (he:0<v) (hp:v≤threshold C 100 0)(hh:((C.path.levels.budget k).B^2+4:ℕ)* C.S.a k<v): arch 100 C v < k:=by
   let j:=arch 100 C v; let f i:= ((B i)^2+4:ℕ)*C.S.a i; have hf:Antitone f:=antitone_nat_of_succ_le (reducing H); by_contra! ht; have hz:= (A.apron j ht).1; have hr:stride C 100 j ≤ (B j)^2+4:= by change stride C 100 j-4≤(B j)^2 at hz; omega
   have hb:= arch_fails 100 he hp; exact hh.not_ge (le_trans hb ((mul_le_mul_of_nonneg_right (by exact_mod_cast hr: (stride C 100 j:ℝ)≤ ((B j)^2+4:ℕ)) (C.S.a_pos j|>.le)).trans (hf ht)))
omit H in
lemma Barrow.down {K:ℕ}{v:ℕ} (A:Barrow C r m K j) (he:j≤ i)(hv:v≤K) : Barrow C r m v i:= ⟨A.hbar.trans he,fun s hs=>by obtain ⟨hp,hX,hh⟩:= A.apron s (he.trans hs); exact ⟨hp,hv.trans hX,hh⟩⟩
end YM.OPE.Strobe

