import YM.RG12.Tavern.Count
/-!
# Serve sharp comparison. Any compatible W frames receiving the locale PT estimate.

No further thermal comparisons here. Quantified absorption: local comparison THROUGH ORDER two
 with eta up to 1/2 (in those two geometric reports themselves, after their preparation),
A*meter^o costs permitted incl powers Λ. Need exact leading into position normalization
(vs WilsonX ret Ω & coupling transform), exact first and second group laws and Taylor
identification as specified. These are still large producer tasks. The PUBLIC reduction still
is on Studies at the SAME Final, k lengths vs reporting μ offsets as quoted above.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Tavern
open Frames Alidade Function Filter Set Lattice RG Rail Real
open Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{h:ℕ}
variable {V:Grade h→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℂ (V i)]
   [FiniteDimensional ℂ (Col V)]
local notation "A!"=>Col V
variable {F:Type}[AddCommGroup F][Module ℂ F]{t:ℕ→ℝ}
variable {P:Col V≃ₗ[ℂ]F}{f:ℝ→Gram.Square F}{q:ℕ→ℝ}
local notation "μ"=> C.path.levels.clock.monitor
variable {l:ℝ}{Q:Wheel V}{K L:ℝ}{lit:ℕ→Prop}{b:ℝ}{o:ℕ}{N:ℕ}
variable (hG:G.Simple)(hQ:Weather Q K)(hχ:Barred (Z:=C.path.levels) q b)
local notation "Λ"=> C.path.levels
include hχ hG hQ
-- prices in W. Tests on W powered by SAME K as its expansion bounds, not same as pivots!
-- installation required eventually at k+1 for purposes of consecutive hop, does not price t k generally
-- Provides ratio on full columns on normalized true F, at common shape orientation.
omit [FiniteDimensional ℂ (Col V)] in
theorem bars (hs:Slugg (Λ))(hl:0<l)(hN:0<N)
 (hW: Plank (C.path.levels) P f q (torchR (Λ) l N) Q lit o) :
    ∃ p:ℕ, ∀ᶠ k:ℕ in atTop,lit k→ lit (k+1) →
     let T (i:ℕ):=torchR (Λ) l N i
     let r:=epoch (Λ) (k+1) /epoch (Λ) k;let u:=T k/T (k+1)
     let ψ(i:ℕ)(x:F):= Real.sqrt ((f (T i)).eval x)
     1 ≤ u ∧ Real.log u ≤ 2*Alidade.slice (Λ) k ∧ ∃ W:Col V≃ₗ[ℂ] F, formative W P ∧ Tests (ψ (k+1)∘W) (2*K) ∧
             ∀ x:A!, ψ k (W (dilate u x)) ≤ r^p*ψ (k+1) (W x) ∧ ψ (k+1) (W x) ≤ r^p * ψ k (W (dilate u x)):=by
   obtain ⟨H⟩:= hQ.prices
   have hK:=H.hex
   have hC:0<K:=zero_lt_one.trans_le hK
   obtain ⟨p,hp⟩:= penny hG hχ o (8*K^2) K (by positivity)
   refine ⟨2*p,?_⟩
   filter_upwards [hW,hp,ratios (Λ) hG l hl N hN hs h 1,block_dial (Λ) hG l hl N hN hs, pennies hG hQ hχ o] with k h1 h2 h3 h4 h5 hk hk' T r u ψ
   obtain ⟨W,hz,HQ⟩:= h1 hk hk'
   have hu:1 ≤ u:=h4.1
   have hL : Real.log u∈ Set.Icc 0 (2*Alidade.slice (Λ) k):=h3.1
   refine ⟨hu,hL.2,W,hz,?_,?_⟩
   all_goals
    let e:=q k; let a:=Real.sqrt e* μ k^o
    let w:=Alidade.slice (Λ) k; have hw:0≤w:=(arc3.trans_le (slice_first ..)).le
    have he:0 ≤ e:=(hχ.positive _).le
    let G(x:A!):=(f (T (k+1))).eval (W x);let Y:= (Q.C).zeroth.val
    let G':=fun x:A!=>(f (T k)).eval (W (dilate u x))
    let z:=(2*a+8*K^2*w)*e^2
    have hR(x:A!):μ k^o * (q k^2*√(q k))*‖x‖^2=a*e^2*‖x‖^2:=by unfold a e; ring
    have hzC(x:A!)(A:Tile (Col V)) (Hh:∀ v y, |A.val v y| ≤ K*‖v‖*‖y‖):|A.val x x| ≤ K*‖x‖^2:=by simpa only [mul_assoc,← pow_two] using Hh x x
    have hlc(x): |G x-Y x x| ≤ (2*K)⁻¹*‖x‖^2:=by
       apply le_trans _ (mul_le_mul_of_nonneg_right (show K*e+K*e^2+a*e^2 ≤ _ from h5) (sq_nonneg ‖x‖))
       have he1 := mul_le_mul_of_nonneg_left (hzC x _ H.one) he; have he2:= mul_le_mul_of_nonneg_left (hzC x _ H.two) (sq_nonneg e)
       have h3 := (HQ x).1
       change |G x-(Y x x+e*Q.C.first.val x x+e^2*Q.C.second.val x x)| ≤ _ at h3
       rw [hR] at h3 -- defeq?
       rw [abs_le] at h3 ⊢; constructor<;>nlinarith only [h3.1,h3.2,he1,he2, mul_le_mul_of_nonneg_left (le_abs_self (Q.C.first.val x x)) he,mul_le_mul_of_nonneg_left (neg_le_abs (Q.C.first.val x x)) he, mul_le_mul_of_nonneg_left (le_abs_self (Q.C.second.val x x)) (sq_nonneg e),mul_le_mul_of_nonneg_left (neg_le_abs (Q.C.second.val x x)) (sq_nonneg e)]
    have hg : Gram.Regular (f (T (k+1))) W.toLinearMap (2*K):=Gram.nonsingular (fun x=>Y x x) hK (fun x=> ⟨(le_abs_self _).trans (hzC x _ H.zero), hQ.pounds _⟩) hlc
   · exact Gram.stable hg
   intro x
   obtain ⟨hx,hX⟩:=sheared hQ u hu x
   have hfg: |G' x-G x| ≤ z*‖x‖^2:=by
      obtain ⟨ha,hb⟩:=HQ x
      unfold G' G
      have hh : 0 ≤ 4*K^2:=by positivity
      have hlc:4*K^2*log u*‖x‖^2 ≤ 8*K^2*w*‖x‖^2:=by
         convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL.2 hh) (sq_nonneg ‖x‖) using 1 <;> first | rfl | unfold w;ring
      replace hX:=mul_le_mul_of_nonneg_left (hX.trans hlc) (sq_nonneg e)
      have hl:= (hQ.flow _ hu x).1
      unfold Alidade.axis at ha hb
      change |(f (T k)).eval (W (dilate u x))-((Q.X u).zeroth.val x x+e*(Q.X u).first.val x x+e^2*(Q.X u).second.val x x)|≤_ at hb
      rw [hl,hx,hR] at hb;rw [hR] at ha
      change |(f (T (k+1))).eval (W x)-(Y x x+e*Q.C.first.val x x+e^2*Q.C.second.val x x)|≤_ at ha
      obtain ⟨ha1,ha2⟩:=abs_le.mp ha;obtain ⟨hb1,hb2⟩:=abs_le.mp hb
      let x2:=(Q.X u).second.val x x-Q.C.second.val x x
      unfold z; unfold Y at *; rw [abs_le]
      constructor<;>nlinarith only [hX,ha1,ha2,hb1,hb2, mul_le_mul_of_nonneg_left (neg_le_abs x2) (sq_nonneg e),mul_le_mul_of_nonneg_left (le_abs_self x2) (sq_nonneg e)] -- x2 transparent?
   let ρ:=r-1; have hr:0 ≤ ρ:=sub_nonneg.mpr (epoch_unit (Λ) k.le_succ)
   have he' := hg.coerc x
   have hgg : 0 ≤ G x:=nonneg_of_mul_nonneg_right ((sq_nonneg _).trans he') (mul_pos zero_lt_two hC)
   let m:ℝ:=(p:ℝ)/(2*K)
   have hm:0 ≤ m:=by unfold m; positivity
   have ht' : 2*K*z ≤ p*ρ:= by simpa only [z,a,e,r,ρ,w, ← mul_assoc] using! h2.1
   have hr1 : z ≤ m*ρ := by unfold m;rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity)]; linarith only [ht']
   have hp : 2*K*m=(p:ℝ):=by unfold m;field_simp
   have h':2*(2*K)*m*ρ ≤ 1:=by rw [mul_assoc 2 (2*K) m,hp]; have hf:(p:ℝ)*ρ ≤ 1/2:=h2.2; linarith
   apply permits (s:= epoch (Λ) k) (s':=epoch (Λ) (k+1)) hgg (norm_nonneg x) he' hm (hfg.trans (mul_le_mul_of_nonneg_right hr1 (sq_nonneg _))) hr _ hp.le h'
   unfold ρ r; linarith only
end YM.RG12.Tavern
