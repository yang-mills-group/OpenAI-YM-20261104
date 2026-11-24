import YM.RegulatorIR.Centered.Cube

/-! Slightly wider domain for cover cell charges (permit a cell outside the
center testing cube, needed if the permitted center cube is small). -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Centered
open Topology Lattice MeasureTheory Set Metric Motion Spatial
open scoped ENNReal NNReal BigOperators Classical
variable {t l a o C:ℝ}

private lemma arrangement (hl:0<l)(hx:l ≤ t)(a o:ℝ) : ∃ (n:ℤ)(m:ℕ),
     a≤o+n*l ∧ o+n*l+m*l≤a+t ∧ t≤m*l+2*l:=by
 let n:= ⌈(a-o)/l⌉; let x:=o+n*l
 have h:a≤x:=by have h:= (div_le_iff₀ hl).mp (Int.le_ceil ((a-o)/l)); unfold x;nlinarith [show ↑n=(⌈(a-o)/l⌉:ℝ) from rfl]
 have hh:x< a+l:=by
    have h₁: (n:ℝ)-1 < (a-o)/l := by have q:= Int.ceil_lt_add_one ((a-o)/l); unfold n; linarith
    have h₂:= (lt_div_iff₀ hl).mp h₁; unfold x;linarith
 let m:=⌊(a+t-x)/l⌋₊
 have hm:a+t-x≥ 0:= by linarith
 have h₁: (m:ℝ)≤(a+t-x)/l:= Nat.floor_le (div_nonneg hm hl.le)
 have h₂:(a+t-x)/l < (m:ℝ)+1:= Nat.lt_floor_add_one _
 refine ⟨n,m,h,?_,?_⟩
 · change x+_≤_; linarith [(le_div_iff₀ hl).mp h₁]
 linarith [(div_lt_iff₀ hl).mp h₂]
private lemma cost {x t l:ℝ}(hl:0≤l)(h:0≤x)(he:x≤t)(hx:t≤x+2*l): t^4-x^4 ≤ 8*l*t^3:=by
 have ht:0≤t:= h.trans he
 calc
 t^4-x^4=(t-x)*(t^3+t^2*x+t*x^2+x^3):=by ring
 _ ≤ (2*l)*(t^3+t^2*t+t*t^2+t^3):= mul_le_mul (by linarith) (by gcongr) (by positivity) (by positivity)
 _ = _:= by ring

lemma stretch {g:Room→ℝ}(H:Rhythm l g) (hl:0<l)(ht:0<t)(hi: IntegrableOn g (cube (same a) t)) (hC:0≤C) (hc: ∀ w∈cube (same a) t,‖g w‖ ≤ C)(hcc: ∀ w∈cube (same o) l,‖g w‖ ≤ C):
   ‖weigh (same a) t g -weigh (same o) l g‖ ≤ 16*C*(l/t) := by
 let P:= weigh (same o) l g; let Q:= cube (same a) t
 rcases le_total t l with hsmall|hy
 · apply (norm_sub_le ..).trans; apply (add_le_add (worth ht hc) (worth hl hcc)).trans
   have hp:(1:ℝ)≤l/t:= (le_div_iff₀ ht).mpr (by simpa using hsmall); nlinarith
 obtain ⟨n,m,hp,hw,hM⟩:= arrangement hl hy a o; let d:= o+n*l
 let R:= block l d m
 have hr:R⊆Q:=enclosure m hl hp hw
 have hd:= block_meas l d m; have hQ:=seen (same a) t
 have hu : (m:ℝ)*l≤ t:= by linarith
 let F:=Q \ R; let v:= t^4-((m:ℝ)*l)^4
 have hv:0≤v:=sub_nonneg.mpr (pow_le_pow_left₀ (by positivity) hu 4)
 have he: volume Q≠⊤:= by rw [cubic _ ht.le]; finiteness
 have hf: volume.real F=v:=by rw [show F=Q\R from rfl,MeasureTheory.measureReal_sdiff hr hd he,block_vol d m hl,Measure.real,cubic _ ht.le, ENNReal.toReal_ofReal (by positivity)]
 let z:=∫ x in F,g x
 have hz: ‖z‖≤ C*v:= by
    rw [← hf]; exact norm_setIntegral_le_of_norm_le_const (lt_of_le_of_lt (measure_mono sdiff_subset) he.lt_top) (fun x (hx:x∈F) =>hc _ hx.1)
 have hh : accrue g (same a) t= z+(m:ℝ)^4*accrue g (same o) l:=by
    change (∫ x in Q, g x)=_
    nth_rw 1 [← sdiff_union_of_subset hr]
    rw [setIntegral_union disjoint_sdiff_self_left hd (hi.mono_set sdiff_subset) (hi.mono_set hr),integrates H _ _ _ hl (hi.mono_set hr)]
 have hX : weigh (same a) t g-P = (z-v*P)/t^4:=by unfold weigh; rw [hh]; unfold v P weigh; field_simp; ring
 change ‖_ - P‖ ≤ _
 rw [hX,norm_div, Real.norm_of_nonneg (pow_nonneg ht.le _)]
 calc
   _ ≤ (2*C*v)/t^4:= by
     gcongr ?_ / _
     apply (norm_sub_le ..).trans
     rw [norm_mul,Real.norm_of_nonneg hv]; apply le_trans (add_le_add hz (mul_le_mul_of_nonneg_left (worth hl hcc) hv)); nlinarith
   _ ≤ (2*C*(8*l*t^3))/t^4:= by gcongr; exact cost hl.le (by positivity) hu hM
   _ = _:= by field_simp; ring
end YM.RegulatorIR.Centered
