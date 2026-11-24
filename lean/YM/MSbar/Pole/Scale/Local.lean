import YM.MSbar.Pole.Scale.Spark

/-! # Local vertex polynomiality after pole subtraction. Keep angular probes. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient Momentum Age Mellin
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I]

structure Local (A : Finset I) (a : ℤ) (H : Cloud I) : Prop where
  regular : Canonical H
  trivial : 0<a → H=0
  weights n x (t:ℝ) (ht:0<t): H n (move A t x)=(t:ℂ)^(-a)*H n x

variable {A : Finset I} {a : ℤ} {H : Cloud I}
namespace Local
lemma zero : Local (I:=I) A a 0 := ⟨⟨⟨fun _ _ _=>rfl,fun _ _=>rfl⟩, fun _=>Packet.zero⟩, fun _=>rfl, fun _ _ _ _=>by simp⟩
lemma add {G : Cloud I} (h : Local A a H) (g : Local A a G) : Local A a (H+G) := by
  refine ⟨⟨h.regular.1.add g.regular.1,fun n=>(h.regular.2 n).add (g.regular.2 n)⟩,fun i=>by rw [h.trivial i,g.trivial i]; simp,?_⟩
  intro n x t ht; simp only [Pi.add_apply,h.weights n x t ht,g.weights n x t ht,mul_add]
lemma neg (h : Local A a H) : Local A a (-H) := by
  refine ⟨⟨⟨fun n J x=>congr_arg Neg.neg (h.regular.1.moves ..),fun n x=>congr_arg Neg.neg (h.regular.1.agrees ..)⟩,fun n=>(h.regular.2 n).neg⟩,fun i=>by rw [h.trivial i]; simp,?_⟩
  intro n x t ht; simp only [Pi.neg_apply,h.weights n x t ht,mul_neg]
lemma number (h : Local A a H) (c : ℂ) : Local A a (c • H) := by
  constructor
  · constructor
    · constructor
      · intro n J x; simp only [Pi.smul_apply,h.regular.1.moves]
      intro n x; simp only [Pi.smul_apply,h.regular.1.agrees]
    intro n; exact (Packet.const c).mul (h.regular.2 n)
  · intro i; rw [h.trivial i]; simp
  intro n x t ht; simp only [Pi.smul_apply,smul_eq_mul,h.weights n x t ht]; ring
lemma echo (h : Local A a H) (t:ℝ) (ht:0<t) (z:ℂ) (n) (x) :
    roll A ⟨a,0⟩ t (fun _=>H) z n x=H n x:= by unfold roll; simp only [h.weights n x t ht]; simp only [alpha,linear,Nat.cast_zero,mul_zero,zero_mul,add_zero,Complex.cpow_intCast,zpow_neg]; exact mul_inv_cancel_left₀ (zpow_ne_zero _ (by exact_mod_cast ht.ne')) _
-- Denote the homogeneous polynomial in momentum coordinates with spectator indices unscaled.
lemma rendition (h : Local A a H) (ha:a≤0) {n:ℕ} (x:External I n) :
    H n x = (a.natAbs.factorial:ℂ)⁻¹ * iteratedFDeriv ℝ a.natAbs (H n) (move A 0 x) (fun _=>charge A n x) := by
  let m:= a.natAbs; have hm: -a=(m:ℤ):= by omega
  let p : ℝ → External I n:= (move A · x)
  let f(t:ℝ) := H n (p t); let g(t:ℝ) := (t:ℂ)^m * H n x
  have hG : EqOn f g (Ioi 0) := fun t ht=>by rw [show f t= _ from h.weights n x t ht,hm,zpow_natCast]
  have hd n : ContDiff ℝ m (H n):=contDiff_iff_contDiffAt.mpr fun x=> (h.regular.2 n).localn m (Set.mem_univ _)
  have hf : ContDiff ℝ m f:=(hd n).comp ((curve_diff A x).of_le (by exact_mod_cast (show (↑m:ℕ∞) ≤ ⊤ from le_top)))
  have hg : ContDiff ℝ m g := ((Complex.ofRealCLM.contDiff.pow m).mul contDiff_const)
  have ht : iteratedFDeriv ℝ m f 0=iteratedFDeriv ℝ m g 0 := by
    refine tendsto_nhds_unique_of_eventuallyEq ((hf.continuous_iteratedFDeriv (m:=m) le_rfl).continuousAt.continuousWithinAt (s:=Ioi 0)) ((hg.continuous_iteratedFDeriv le_rfl).continuousAt.continuousWithinAt) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ((show f =ᶠ[𝓝 t] g from mem_of_superset (isOpen_Ioi.mem_nhds ht) fun i hi=> hG hi).iteratedFDeriv ℝ m).eq_of_nhds
  let L : ℝ→L[ℝ] External I n:= (ContinuousLinearMap.id ℝ ℝ).smulRight (charge A n x)
  let B:ℝ→L[ℝ]ℂ:= ((ContinuousLinearMap.id ℝ ℝ).smulRight (H n x))
  have hb : g = B ∘ fun t=>t^m := by funext t; change _= (t^m) • H n x; simp [g,Complex.real_smul]
  have hl(s):move A 0 x+ L s=p s:=by change move A 0 x+s • _=_; unfold p; rw [moving,moving]; simp only [sub_smul,one_smul,zero_sub,neg_smul]; abel
  let e : Fin m→ℝ := 1; let P := charge A n x
  have hy : (fun y:Fin m=>L (e y))=fun _=>P:=by funext y; change (1:ℝ) • P=P; rw [one_smul]
  rw [hb,B.iteratedFDeriv_comp_left (n:=↑m) (by fun_prop) le_rfl, show f=fun t=>H n (move A 0 x+L t) from funext fun t=>congr_arg _ (hl t).symm,
      iter_affine (φ:=H n) L _ 0 m (hd _).contDiffAt,map_zero,add_zero] at ht
  have he := congr_arg (fun W:ContinuousMultilinearMap ℝ (fun _:Fin m=> ℝ) ℂ=> W e) ht
  change iteratedFDeriv ℝ m _ _ (fun y=> L (e y))= B (iteratedDeriv m _ _) at he -- maybe defeq
  change H n x=(m.factorial:ℂ)⁻¹*_
  rw [hy, iteratedDeriv_pow] at he; rw [show iteratedFDeriv ℝ m (H n) (move A 0 x) (fun _=>charge A n x)= _ from he];
  simp only [Nat.descFactorial_self, Nat.sub_self,pow_zero,mul_one]
  change H n x= (m.factorial:ℂ)⁻¹*((m.factorial:ℝ) • H n x); rw [Complex.real_smul]; push_cast; exact (inv_mul_cancel_left₀ (show (m.factorial:ℂ)≠0 by exact_mod_cast m.factorial_ne_zero) _).symm
end Local
end YM.MSbar.Pole
