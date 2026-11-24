import YM.RG17.Pitch
import YM.Pier.Lair.Lit

/-! iterations ANY center near scale within polynomial ratio, both capture directions & upper & lower. Proof genuinely transfers across two frames; True annulus Fits still requires the grade relation ACROSS levels and much sharper than these costs over polynomial apertures. No claim of Sharp coefficient or frame morphisms in the PT sense. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Lair
open Function Filter Set Table Extraction Climb Analysis Ward Spec
open Trace Trace.Over Trace.Terrace Trace.Pilot MergeProof.East Next.Rank
open Next.UVStress Spin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{f : Extraction.Order}{S:Table C.book}
variable (F: Final C f S) (h:G.Simple) {H : (Bel C.book).Hierarchy}
set_option quotPrecheck false
local notation "B" => (Bel C.book)
local notation "θ" => Maxwell.Free.spin_free C.labels
local notation "τ" => (turns C)
local notation "W₀" => (Maxwell.Free.scheme C.book.grid)
local notation "W₁" => F.sector.derivatives
local notation "H₀" => Maxwell.Free.hierarchy C.labels
local notation "H₁" => F.room.kernel
local notation "τ₁" => F.sector.turns
variable {X:Scaling S}{l: Ultrafilter (ℕ×ℕ)}{Z:Arch C}{V:∀ i, Vane C i}
open MeasureTheory SharpGram Lenses
open scoped ContDiff

variable {Y:ℝ→FamilyBasis (C:=C) S} (P:Present F Y) (d:ℕ)
open Weak.Portfolio OPE.Levy Push.FiniteDetection.Free
local notation "D₂"=> detectors
local notation "W₂"=>Pilot.trail
local notation "U!"=> (glass (Bel C.book) θ d)
local notation "K!"=> (glass S (H₁).spin d)
local instance (V:Gauge)(T:Register V)(L:Table T)(d:ℕ): FiniteDimensional ℝ (L.Field d) := Module.Finite.trans ℂ _

section connections
variable {A E : Type*}[NormedAddCommGroup A][NormedSpace ℂ A][AddCommGroup E][Module ℂ E] {U X Z:A ≃ₗ[ℂ] E} {c c' : ℝ}
namespace Both
lemma one (U:A ≃ₗ[ℂ] E) : Both 1 U U:= ⟨fun v=>by simp,fun v=>by simp⟩
lemma larger (h:Both c U X)(he:c≤ c') : Both c' U X:= ⟨fun x=>(h.left x).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _)),fun x=>(h.right x).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))⟩
lemma swap (h:Both c U X) : Both c X U:=⟨h.right,h.left⟩
lemma trans (h:Both c U X)(he:Both c' X Z)(hc:0 ≤ c)(hc':0 ≤ c'): Both (c*c') U Z := by
   refine ⟨fun x => le_trans (h.left x) ((mul_le_mul_of_nonneg_left (he.left x) hc).trans_eq (mul_assoc ..).symm),fun x => le_trans (he.right x) ((mul_le_mul_of_nonneg_left (h.right x) hc').trans_eq ?_)⟩; ring
end Both
end connections

include P
local notation "F!" => F
lemma ranges : ∃ k:ℕ, ∃ t:ℝ, 0<t ∧∀ r s:ℝ, 0<r → r ≤ s → s ≤ t → Both ((2*s/r)^k) (Y r d) (Y s d):= by
   obtain ⟨K,hK,L,hL,h⟩:= throughout F P d
   obtain ⟨k,hkΩ⟩:=pow_unbounded_of_one_lt K (one_lt_two : (1:ℝ)<2); let u:ℝ:=2^k; have hu:1 ≤ u:= one_le_pow₀ one_le_two
   have hh(n) (r s:ℝ) (hv:0<r) (hp:r ≤ s)(he:s ≤ L)(hr:s ≤ r*2^n): Both (u^n) (Y r d) (Y s d):=by
       induction n generalizing r with
       | zero => have ht:s ≤ r:=by simpa using hr
                 rw[le_antisymm hp ht]; rw [pow_zero]; apply Both.one
       | succ n ih =>
           by_cases hs:s ≤ 2*r
           · exact (h r s hv hp he hs).larger (hkΩ.le.trans (by rw [pow_succ];exact le_mul_of_one_le_left (zero_le_one.trans hu) (one_le_pow₀ hu)))
           push Not at hs; have hy:= (h r (2*r) hv (by linarith) (hs.le.trans he) le_rfl).larger (show K ≤ u from hkΩ.le)
           have hZ:= ih (2*r) (by positivity) hs.le (hr.trans_eq (by rw [pow_succ]; ring))
           rw [pow_succ']; exact hy.trans hZ (zero_le_one.trans hu) (pow_nonneg (zero_le_one.trans hu) _)
   refine ⟨k,L,hL,fun r s hr hs ht=> ?_⟩
   have h0:0<s:=hr.trans_le hs; obtain ⟨n,hn⟩:=pow_unbounded_of_one_lt (s/r) (one_lt_two:(1:ℝ)<2); have hx:∃ n:ℕ,s/r ≤ 2^n:=⟨n,hn.le⟩; let q:=Nat.find hx; have hq:s/r ≤ 2^q:=Nat.find_spec hx
   have hk: (2:ℝ)^q ≤ 2*s/r:=by
       cases he:q with
       | zero=> rw [pow_zero]; exact (le_div_iff₀ hr).mpr (by linarith)
       | succ i => have he: q > i:=he ▸ Nat.lt_succ_self i
                   have hx: (2:ℝ)^i < s/r:=lt_of_not_ge (fun h=> not_le_of_gt he (Nat.find_min' hx h))
                   rw[pow_succ]; rw[mul_div_assoc]; linarith
   refine (hh q r s hr hs ht (((div_le_iff₀ hr).mp hq).trans_eq (mul_comm ..))).larger (le_trans (b:=((2:ℝ)^q)^k) ?_ (pow_le_pow_left₀ (by positivity) hk _))
   apply le_of_eq; unfold u; rw [← pow_mul,Nat.mul_comm,pow_mul]

local notation "β"=> C.path.levels.clock.hatBeta
local notation "δ"=>Lenses.margin C d/2
variable {u : Filter (ℕ×ℕ)} (Q : Mantle F u) (E : OPE.Services C f S)
open Load
omit P
include E
lemma glint : Tendsto (fun i:ℕ=>arcPrice F d (tent Q i d) (Q.radius i • D₂)) atTop (𝓝 (Weak.Portfolio.model C d)):=by
   have h:= Q.reaches d
   let R(i:ℕ)(x:(B).Field d):= (Q.lens i d).symm (tent Q i d x)
   apply formsLimits _ _; intro x y
   have hx:= (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds (seats Q E (x:=fun _=>x) tendsto_const_nhds))
   have hy:= (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hx.prodMk_nhds (seats Q E (x:=fun _=>y) tendsto_const_nhds))
   refine hy.congr fun i=> ?_
   change K! _ (Q.lens i d ((Q.lens i d).symm _)) (Q.lens i d ((Q.lens i d).symm _))= K! _ _ _; rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]; rfl
omit E in
private lemma quote_m {r:ℝ} {Y Y':Spin.change S d} (h:coercive (arcPrice F d Y (r•D₂)) δ) (hr:coercive (arcPrice F d Y' (r•D₂)) δ)
   {K:ℝ} (hK:0 ≤ K) (hp:‖arcPrice F d Y (r•D₂)‖ ≤ K) (hP:‖arcPrice F d Y' (r•D₂)‖ ≤ K): Both (Real.sqrt (K/(δ))) Y Y':= by
   have hz(A₁ A₂:Spin.change S d)(h:coercive (arcPrice F d A₁ (r•D₂)) δ)(ht:‖arcPrice F d A₂ (r•D₂)‖ ≤ K)(x:S.Field d): ‖A₁.symm x‖ ≤ Real.sqrt (K/(δ)) * ‖A₂.symm x‖:=by
       apply bodyBound (half_pos ((Weak.Portfolio.freely (C:=C) d).choose_spec.1)) hK (norm_nonneg _) (norm_nonneg _)
       apply (h (A₁.symm x)).trans
       calc
         _ = arcPrice F d A₂ (r • D₂) (A₂.symm x) (A₂.symm x) := by
              change K! _ (A₁ (A₁.symm _)) (A₁ (A₁.symm _))=K! _ (A₂ (A₂.symm _)) (A₂ (A₂.symm _)); rw[LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
         _ ≤ _:= (realUpper ..).trans (mul_le_mul_of_nonneg_right ht (sq_nonneg _))
   exact ⟨hz Y Y' h hP, hz Y' Y hr hp⟩
include P
lemma travails : ∃ K:ℝ,0 < K∧ ∀ᶠ i:ℕ in atTop, Both K (tent Q i d) (Y (Q.radius i) d):=by
   let Z:=Weak.Portfolio.model C d; let x:=δ+‖Z‖; have hδ:0 < (δ):=half_pos (Weak.Portfolio.freely (C:=C) d).choose_spec.1; have hx:0 < x:=add_pos_of_pos_of_nonneg hδ (norm_nonneg Z)
   refine ⟨Real.sqrt (x/(δ)),by positivity,?_⟩
   filter_upwards[stayNear (glint F d Q E) hδ,(RG17.homes Q).eventually (heights F P d)] with i hi ⟨hh,hV⟩
   exact quote_m F d (absorb _ _ (Lenses.margin C d) (δ) ((Weak.Portfolio.freely (C:=C) d).choose_spec.2) (by simpa only [sub_half] using hi)) hh hx.le (normBy hi) hV
open RG17
lemma across (p:ℝ→ℕ)(ht : Tendsto p Pilot.trail atTop)(hs:∀ᶠ r in Pilot.trail, C.S.a (p r)≤r ∧ r ≤ C.S.a (p r)*β (p r)^2):
    ∃ K:ℕ,∀ᶠ r in Pilot.trail,Both (β (p r)^K) (tent Q (p r) d) (Y r d):=by
   obtain ⟨k,L,hL,h⟩:=ranges F P d
   obtain ⟨c,hc,hx⟩:= travails F P d Q E
   refine ⟨1+3*k,?_⟩
   have hv:= Station.hat_rate C.path.levels E.simpleGate
   filter_upwards [ht.eventually hx,(hv.comp ht).eventually_ge_atTop c,(hv.comp ht).eventually_ge_atTop 2,
      hs, ht.eventually Q.proper, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ge_mem_nhds hL), (Q.small.comp ht).eventually (ge_mem_nhds hL)] with r hk hP hB hr hQ hp h' hv
   let m:=p r; let a:= C.S.a m; let b:=β m; let s:=Q.radius m
   have hy: 0<s:=Q.positive _; have hp':0<r:=hp; have ha:0<a:= C.S.a_pos _; have he:2 ≤ b:= hB; have he':0<b:=zero_lt_one.trans_le (one_le_two.trans he)
   have hx (x y:ℝ)(ht: a ≤ y)(hw:x ≤ a*b^2):2*x/y ≤ b^3:=by
       refine (div_le_iff₀ (ha.trans_le ht)).mpr ?_
       rw [pow_succ]
       apply le_trans (b:=2*(a*b^2)) (by linarith only [hw]); nlinarith only [mul_le_mul_of_nonneg_left he (mul_nonneg ha.le (sq_nonneg b)), mul_le_mul_of_nonneg_left ht (mul_nonneg (sq_nonneg b) he'.le)]
   have hu z (h:0 ≤ z) (he:z ≤ b^3): c*z^k ≤ b^(1+3*k):=by
       rw [pow_add,pow_one,pow_mul]; exact mul_le_mul hP (pow_le_pow_left₀ h he _) (pow_nonneg h _) he'.le
   rcases le_total r s with he|he
   · apply ((Both.trans hk (h r s hp' he hv).swap hc.le (pow_nonneg (by positivity) _))).larger; apply hu _ (by positivity) (hx _ _ hr.1 hQ.2)
   apply ((Both.trans hk (h s r hy he h') hc.le (pow_nonneg (by positivity) _))).larger; exact hu _ (by positivity) (hx _ _ hQ.1 hr.2)
end YM.Pier.Lair
