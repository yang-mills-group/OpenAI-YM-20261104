import YM.OPE.Compatible.Kale.Ban
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
namespace PriceZ
variable {W L: Type}
abbrev Cash (M: W→Side) (u:ℕ)(q:W→ℝ)(p:W→ℝ): Prop:= ∃ c:ℝ,0 ≤ c∧∀ i:W,‖p i‖≤ c*((M i).val:ℝ)^u * q i
-- nonnegative quote require separate
variable {M:W→Side} {C:W→Type} [∀ i, NormedAddCommGroup (C i)][∀ i, NormedSpace ℝ (C i)]
variable {s u v:ℕ}{p q:W→ℝ}
variable {A B X: (i:W)→ C i→ℝ}
lemma gold_plus {a b:W→ℝ}(h:Cash M u p a)(hh:Cash M u p b): Cash M u p (a+b):=by
    obtain ⟨c,hc,Hc⟩:=h; obtain ⟨d,hd,Hd⟩:=hh; refine ⟨c+d,add_nonneg hc hd,fun i=> ((norm_add_le (a i) (b i)).trans (add_le_add (Hc i) (Hd i))).trans_eq ?_⟩; ring
lemma gold_times {a b:W→ℝ}(h:Cash M u p a)(hp:0 ≤ p)(hh: Cash M v q b): Cash M (u+v) (p*q) (a*b):=by
    obtain ⟨c,hc,Hc⟩:=h; obtain ⟨d,hd,Hd⟩:=hh; refine ⟨c*d,mul_nonneg hc hd,fun i=>?_⟩; rw [Pi.mul_apply,norm_mul]; have he:0 ≤ p i:=hp i; refine (mul_le_mul (Hc i) (Hd i) (norm_nonneg _) (by positivity)).trans_eq ?_; rw [pow_add,Pi.mul_apply]; ring
abbrev care (C:W→Type)[∀ i, Norm (C i)](u k:ℕ)(c:W→ℝ)(M:W→Side)(x:W)(i:C x):= ((M x).val:ℝ)^u*c x * (1+‖i‖)^k
-- bound.F precision secondary
structure WindZ (M:W→Side)(u k:ℕ)(q:W→ℝ)(A: (i:W)→ C i→ℝ):Prop where
      cap: ∃ c:ℝ,0≤c ∧∀ i x, ‖A i x‖ ≤ c*care C u k q M i x
      zon (i:W): Bond (A i)
variable (h:WindZ M u k p A)
lemma W_le (m: Side):1 ≤ (m.val:ℝ):= Nat.one_le_cast.mpr m.pos
include h
lemma WindZ.gauge (hp:0 ≤ p)(hq:p ≤ q)(hx:u ≤ v)(ht:k ≤ s): WindZ M v s q A:=by
    obtain ⟨c,hc,H⟩:=h.cap; refine ⟨⟨c,hc,fun i x=>(H i x).trans ?_ ⟩,h.zon⟩; have hv:0≤q i:=le_trans (hp i) (hq i); unfold care; gcongr <;>first | exact W_le _ | exact hp i| exact hq i| positivity| simp
omit h in
lemma WindZ.zero (M:W→Side)(u k:ℕ)(p:W→ℝ): WindZ M u k p (fun i=> (0:C i→ℝ)):= ⟨⟨0,le_rfl,fun i x=>by rw [Pi.zero_apply,norm_zero,zero_mul]⟩,fun i=>Bond.zero⟩
lemma WindZ.add (H:WindZ M u k p B) :WindZ M u k p (A+B):=by
   obtain ⟨c,hc,hA⟩:= h.cap; obtain ⟨v,hv,hv'⟩:= H.cap; exact ⟨⟨c+v,add_nonneg hc hv,fun i x=> ((norm_add_le ..).trans (add_le_add (hA i x) (hv' i x))).trans_eq (add_mul ..).symm⟩,fun i=> (h.zon i).add (H.zon i)⟩
lemma WindZ.neg : WindZ M u k p (-A):=by obtain ⟨c,hc,hA⟩:=h.cap; exact ⟨⟨c,hc,fun i x=> by simpa only [Pi.neg_apply,norm_neg] using hA i x⟩,fun x=>(h.zon x).neg⟩
lemma WindZ.sub (H:WindZ M u k p B): WindZ M u k p (A-B):=by rw [sub_eq_add_neg]; exact h.add H.neg
lemma WindZ.mul (H:WindZ M v s q B) (hp:0≤ p):WindZ M (u+v) (k+s) (p*q) (A*B):=by
    obtain ⟨c,hc,hA⟩:= h.cap; obtain ⟨d,hd,hB⟩:= H.cap; refine ⟨⟨c*d,mul_nonneg hc hd,fun i x=>?_⟩,fun i=> (h.zon i).mul (H.zon i)⟩; rw [Pi.mul_apply,Pi.mul_apply,norm_mul]; refine (mul_le_mul (hA i x) (hB i x) (norm_nonneg _) (by have he:0 ≤ p i:=hp i; unfold care; positivity)).trans_eq ?_; unfold care; rw [pow_add,pow_add,Pi.mul_apply];ring
lemma WindZ.smul (c: ℝ): WindZ M u k p (c • A):=by obtain ⟨d,hd,H⟩:=h.cap; refine ⟨⟨‖c‖*d,mul_nonneg (norm_nonneg _) hd,fun i x=>?_⟩,fun i=>(h.zon _).scale _⟩; rw [Pi.smul_apply,Pi.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left (H i x) (norm_nonneg _)).trans_eq (mul_assoc ..).symm
lemma WindZ.scale {a:W→ℝ}(ha:Cash M v q a)(hq:0 ≤ q): WindZ M (v+u) k (q*p) (fun i=>a i • A i):=by
       let f(i:W)(_ : C i):ℝ:=a i; have hg: WindZ M v 0 q f:=by obtain ⟨d,hd,H⟩:=ha; refine ⟨⟨d,hd,fun i x=>(H i).trans_eq ?_⟩,fun i=>Bond.keep _⟩; unfold care;rw [pow_zero,mul_one,mul_assoc]
       rw [← zero_add k]; -- changes k mismatch with A dependent h? A arbitrary
       exact hg.mul h hq
omit h
lemma WindZ.unit (M:W→Side)(u k:ℕ): WindZ M u k 1 (fun i=> (1:C i→ℝ)):=by refine ⟨⟨1,zero_le_one,fun i x=>?_⟩,fun i=>Bond.one⟩; rw [Pi.one_apply,norm_one,one_mul]; unfold care; rw [Pi.one_apply,mul_one]; apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ (W_le ..)); exact one_le_pow₀ (by simp)
-- constants.Growth vector norm.Project.R.
abbrev WindT (M:W→Side)(u k:ℕ)(q:W→ℝ)(A: (i:W)→ ScriptJ (C i)):Prop:=∀ j:Phase,PriceZ.WindZ M u k q fun i x => (A i x).seq j.val
variable {t B: (i:W)→ScriptJ (C i)}(hh:WindT M u k p t)
include hh
lemma WindT.gauge (hp:0 ≤ p)(hq:p ≤ q)(hx:u ≤ v)(ht:k ≤ s): WindT M v s q t:=fun i=> WindZ.gauge (hh i) hp hq hx ht
omit hh in
lemma WindT.zero (M:W→Side)(u k:ℕ)(p:W→ℝ):WindT M u k p (fun i=>(0:ScriptJ (C i))):=by intro i; fin_cases i<;> exact WindZ.zero ..
lemma WindT.add (hp:WindT M u k p B): WindT M u k p (t+B):=by intro i;fin_cases i <;>first |exact (hh 0).add (hp 0)|exact (hh 1).add (hp 1)|exact (hh 2).add (hp 2)
lemma WindT.sub (hp:WindT M u k p B): WindT M u k p (t-B):=by intro i;fin_cases i <;>first |exact (hh 0).sub (hp 0)|exact (hh 1).sub (hp 1)|exact (hh 2).sub (hp 2)
lemma WindT.prod (H:WindT M v s q B)(hp:0≤p): WindT M (u+v) (k+s) (p*q) (t*B):=by intro i;fin_cases i; exact (hh 0).mul (H 0) hp; exact ((hh 0).mul (H 1) hp|>.add ((hh 1).mul (H 0) hp)); exact (((hh 0).mul (H 2) hp|>.add ((hh 1).mul (H 1) hp)).add ((hh 2).mul (H 0) hp))
end PriceZ
end YM.OPE.Quit
