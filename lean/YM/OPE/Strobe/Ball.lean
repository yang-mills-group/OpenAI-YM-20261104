import YM.OPE.Strobe.Radar
/-! # At every later stencil size and price. Bakery filter. -/
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
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
local notation "B" => ((fun i=>(C.path.levels.budget i).B))
local notation "X" => (C.path.levels.clock.hatBeta)
include H
-- B→∞ eventually
lemma coverV (n:ℕ) : ∀ᶠ i in atTop, n ≤ (C.path.levels.budget i).B := by
    have hc:= Therm.log_raised («K»:=T) H.tune; filter_upwards [hc.eventually_ge_atTop ((n:ℝ)+1)] with i hi; let w:= Real.log (X i); have hp:w^2 ≤ (B i:ℝ):= Nat.le_ceil _
    apply (Nat.cast_le (α:=ℝ)).mp; exact le_trans (by change (n:ℝ)+1 ≤ w at hi; nlinarith only [hi,Nat.cast_nonneg (α:=ℝ) n]) hp
-- t quanta width (generic f cut price)
private lemma acquireV (t:ℕ) : ∀ᶠ i:ℕ in atTop, Loom.stride C t i-4 ≤ (B i)^8:= by
    -- B scale caps.Next.P
    have hw:Tendsto (fun i=>Real.log (X i)) atTop atTop:= Real.tendsto_log_atTop.comp (exists_hat C H.tune)
    filter_upwards [(hw.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (3*t+4:ℝ)] with i hi; unfold stride; rw [Nat.add_sub_cancel]; apply le_trans _ (pow_le_pow_right₀ (by exact (C.path.levels.budget i).B_pos) (by decide: 2≤8)); rw [pow_two]; apply Nat.mul_le_mul_left; let a:=Real.log (X (i+1)); have h:3*t+4≤a:=hi; have hx:(Loom.count C t i:ℝ) ≤ t*a+1:= Loom.count_le
    let f:ℕ:= B i; let g:ℕ:= B (i+1); have hf:a^2 ≤ (g:ℝ):= Nat.le_ceil _; have hg: (g:ℝ)^2 ≤ 2*(f:ℝ)^2:= by exact_mod_cast H.cuts.tabs.grows i
    have hv: (g:ℝ) ≤ 2*(f:ℝ):= by nlinarith [pow_le_pow_left₀ (show 0 ≤ (f:ℝ) by positivity) (show (f:ℝ) ≤ (2:ℝ)*f by simp [two_mul]) 2];
    exact_mod_cast (show (Loom.count C t i:ℝ)+2 ≤ f from by nlinarith only [hv,h,hx,hf,Nat.cast_nonneg (α:=ℝ) t])
private lemma latch (T₀: Citizen C W r D) (d:ℕ) : ∀ᶠ i:ℕ in atTop, 2*muzzle C.path.levels i (omen C d i (B i)) < B i ^8 :=by
    filter_upwards [(Therm.log_raised («K»:=T) H.tune).eventually_ge_atTop 1,coverV H (BasisCost.extent (C.localSection d)),coverV H 100] with i hz ht hs; let k:= B i; let x:=(T|>.clock.J i); have h:x ≤ k:= by
       apply (Nat.cast_le (α:=ℝ)).mp; let z:=Real.log (X i); have hp:1≤z:=hz; have hx:100000*((x:ℝ)+1) ≤ z:= (T₀.safeguards.stage i).pedestal; have hf:z^2 ≤ (k:ℝ):= Nat.le_ceil _; nlinarith only [hp,hx,Nat.cast_nonneg (α:=ℝ) x,hf]
    let b:= BasisCost.extent (C.localSection d); change 2*(b+(k*(4*k+2)+2*k+8)+30*(x+5))<k^8; change b≤k at ht; change 100 ≤ k at hs; have hα:k^3≤ k^8:= pow_le_pow_right₀ (by omega) (by decide:3≤8); nlinarith only [mul_le_mul_of_nonneg_right hs (Nat.zero_le (k^2)),ht,hs,hα,h]
omit H
variable {k n: I→ℕ}{w y:I→ℝ}{φ: Filter I}
local notation "a" => C.S.a
local notation "e" => C.S.scale ∘ k
local notation "l" i => (B (k i))
local notation "ζ'" i=> (C.S.a (k i)*(n i:ℝ))
-- k→∞, native ℓ lane eventually valid Price.C.We write ALL measurements.N≥k incl.Extract.
def chapter (C:Family G)(k n:ℕ):= arch 100 C (C.S.a k*n/4)
-- I finity remove required.`Lace`
structure GracesP (C:Family G)(φ:Filter I)(k n:I→ℕ) : Prop where
    seeks : Tendsto k φ atTop
    ear : Cheap φ (C.S.scale ∘ k) (fun i=> (n i:ℝ))
    pace : ∀ᶠ i in φ, (C.path.levels.budget (k i)).B^8 ≤ n i
variable (L : GracesP C φ k n)
include L
omit [Fintype I] [DecidableEq I] in
lemma GracesP.vv : ∀ᶠ i in φ,0< n i:= L.pace.mono fun i hi=> lt_of_lt_of_le (pow_pos (C.path.levels.budget (k i)|>.B_pos) (8:ℕ)) hi
omit [Fintype I] [DecidableEq I] in
lemma GracesP.ages : Height C.S φ (C.S.scale ∘ k) k 1:= by refine ⟨L.seeks,tendsto_const_nhds.congr' ?_⟩; filter_upwards [(C.S.divergent.comp L.seeks).eventually_gt_atTop 0] with i hi; exact (div_self (ne_of_gt (show 0<C.S.scale (k i) from hi))).symm
local notation "j!" => (fun i=> chapter C (k i) (n i))
include H
omit [Fintype I] [DecidableEq I] in
lemma footing {j:I→ℕ} (Z' : j=fun i=>chapter C (k i) (n i)) : Height C.S φ (C.S.scale ∘ k) j 1 ∧ Bi φ (C.S.scale ∘ k) (fun i=>C.S.a (j i)) (fun i=>C.S.a (k i)) ∧ Tendsto (fun i=> (ζ' i)/4) φ (𝓝[>]0):= by
    subst j; have hδ : Height C.S φ e k 1:= L.ages; have hT:= C.S.divergent.comp L.seeks; have he:Coins φ e (fun i=> (n i:ℝ)):= Coins.by_le L.ear (L.vv.mono fun i hi=> by apply le_trans _ (Real.le_norm_self _); exact_mod_cast hi); let v i:= (C.S.a (k i)*(n i:ℝ))/4
    have hx : Bi φ e v (fun i=>C.S.a (k i)):=by unfold v; simp_rw [div_eq_mul_inv, mul_assoc]; simpa only [mul_one] using Bi.mul (Bi.refl φ e (fun i=> C.S.a (k i))) (Coins.mul he (Bi.const (4:ℝ)⁻¹ (by norm_num) hT))
    have hv:∀ᶠ i in φ,0<v i:= L.vv.mono fun i hi => div_pos (mul_pos (C.S.a_pos (k i)) (Nat.cast_pos.mpr hi)) (by norm_num); have h:= known hT hx hδ.mesh hv; have hc:Tendsto v φ (𝓝[>]0):= tendsto_inf.mpr ⟨h.tends (by norm_num) hT,tendsto_principal.mpr hv⟩; obtain ⟨h',H⟩:= arch_space 100 C hc hT h H.cuts.tabs; exact ⟨h',H.trans hx,hc⟩
omit [Fintype I] [DecidableEq I] in
lemma bolted (T₀ : Citizen C W r D) (d t:ℕ) {κ:ℕ} (hb : Barrow C r m κ z)(hz:C.ref 0< z) : ∀ᶠ i in φ, Passage C d (chapter C (k i) (n i)) (k i) (n i) m z κ r (B (k i)) t:=by
    obtain ⟨h,H',hf⟩:= footing H L (j:=j!) rfl; let c:= (a) m; let d' i:= (B i)^8; have hc:0<c:= C.S.a_pos m; have hv:= C.S.divergent; have hy : Tendsto (fun i=>C.S.a i*(d' i:ℝ)) atTop (𝓝 0):= ((RateLE.mul ((first_price (C:=C)).mesh.pays hv) (rapid hv (show Cheap atTop C.S.scale (fun i=>(d' i:ℝ)) from by unfold d'; push_cast; exact Cheap.power (covers_p (C:=C) hv first_price|>.up) hv _) (RateLE.const 1 hv))).tends (by norm_num) hv)
    obtain ⟨M,hM⟩:= eventually_atTop.mp (near_center C m d H.seed) -- bracket.args
    filter_upwards [h.grows.eventually_gt_atTop z,hf.eventually (Ioc_mem_nhdsGT (lt_of_lt_of_le (C.S.a_pos 0) (gate_b (C:=C) 100 _))),hf.eventually (Ioc_mem_nhdsGT (show 0<c/64 by positivity)),L.pace,L.seeks.eventually_ge_atTop z,L.seeks.eventually_ge_atTop (C.ref d), L.seeks.eventually (acquireV H t), L.seeks.eventually (latch H T₀ d), L.seeks.eventually (coverV H 100),L.seeks.eventually (hy.eventually (gt_mem_nhds (show 0<c/8 by positivity))), L.seeks.eventually (GridApprox.tail_zero (T) |>.eventually (gt_mem_nhds (show 0<c/8 by positivity))), L.seeks.eventually_ge_atTop M] with i hx ⟨hi,hvπ⟩ hβ ht he hi' hK hg hZ hU hL hZ'
    let b:= l i; have hx: z < j! i:= hx; let y:= k i; let F:= n i; let f:=a y; have h:b^8 ≤ n i :=ht; have hβ':f*(n i:ℝ)/4 ≤ c/64:=hβ.2; have hp:0<f:= (C.S.a_pos _); refine ⟨hz,hx, bars2 H (hb.down (C:=C) he (le_refl _)) hi hvπ ?_, hb, ?_, rfl,hvπ, ht,hg,hK,?_, hi',fun N hN=> hM N (hZ'.trans hN) ((hb.hbar.trans he).trans hN)⟩
    · change _ * f < f*(n i:ℝ)/4; have h:b^2+4 ≤ b^3:= by change 100≤b at hZ; nlinarith only [hZ, mul_le_mul_of_nonneg_right hZ (Nat.zero_le (b^2))]
      have hf:4*b^3 < b^8:= by change 100 ≤ b at hZ; have hc : b^4 ≤ b^8:= pow_le_pow_right₀ (by omega) (by decide: 4 ≤ 8); nlinarith only [Nat.mul_le_mul_right (b^3) hZ, hc,hZ, pow_le_pow_right₀ (show 1≤b by omega) (by decide:1≤3)] -- binder b syntax
      rw [lt_div_iff₀ (by norm_num)]; refine lt_of_le_of_lt ?_ (mul_lt_mul_of_pos_left ((by exact_mod_cast hf.trans_le ht) : (((4*b^3:ℕ):ℕ):ℝ) < (n i:ℝ)) hp); push_cast; change ( ( (b:ℝ)^2+4)*_)*_≤ _; have hδ: (b:ℝ)^2+4 ≤ (b:ℝ)^3:= by exact_mod_cast h
      linarith only [mul_le_mul_of_nonneg_left hδ hp.le]
    · unfold f y c at hβ'; linarith only [hβ']
    unfold GridApprox.room; let eQ:= (omen C d y (B y)); have hh:eQ ≤ b ^ 8:=by change 2*(eQ+_) < b^8 at hg; omega
    push_cast; have he₀: f*(b:ℝ)^8 < c/8:=by rw [← Nat.cast_pow]; exact hU
    have he:(omen C d (k i) (B (k i)):ℝ) ≤ (b:ℝ)^8:= by exact_mod_cast hh
    change GridApprox.tail T (k i)< c/8 at hL; change 2*(f*((n i:ℝ)+_)+_) < c; nlinarith only [he₀, hβ', hL, mul_le_mul_of_nonneg_left he hp.le,hc]
end YM.OPE.Strobe

