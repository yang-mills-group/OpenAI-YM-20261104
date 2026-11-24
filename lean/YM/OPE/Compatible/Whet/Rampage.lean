import YM.OPE.Compatible.Whet.Mottle
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {W:Type}{X:W→Type}[∀ i,NormedAddCommGroup (X i)][∀ i,NormedSpace ℝ (X i)]
lemma WindZ.BoostF {u:ℕ}{μ:W→Side}{q:W→ℝ}(p:(i:W)→X i→ℝ)(h:WindZ μ u k q p)(hp:0≤q) : ∃ f:(i:W)→X i→ℝ, WindZ μ u (k+k) q f ∧ ∀ i x, ‖p i x‖ ≤ f i x:=by
   obtain ⟨v,hv,H⟩:=h.cap; let s (i):= v*((μ i).val:ℝ)^u*q i; let t(i:W)(x:X i):= (1+‖x‖)^k; let f(i:W)(x:X i):= p i x/s i
   have hh(i):0 ≤ s i:=by have hx:0 ≤ q i:=hp i;unfold s;positivity
   have he(i x):‖p i x‖≤ s i*t i x:=(H i x).trans_eq (by unfold s t care; ring)
   have ht(i x):p i x=f i x*s i:= by
     by_cases h:s i=0; · have ht:= he i x; rw [h,zero_mul,norm_le_zero_iff] at ht; rw [h,mul_zero,ht]
     exact (div_mul_cancel₀ _ h).symm
   have hl(i x):‖f i x‖≤t i x:=by
     by_cases h:s i=0; · rw [show f i x=0 from by unfold f; rw [h, div_zero]]; rw [norm_zero]; exact pow_nonneg (by positivity) _
     have hv:0 < s i:=lt_of_le_of_ne (hh i) (Ne.symm h); unfold f; rw [norm_div,Real.norm_of_nonneg (hh i),div_le_iff₀ hv,mul_comm]; exact he i x
   let g(i:W)(x:X i):= (1+(f i x)^2)*s i
   have hx(i x):‖p i x‖≤ g i x:=by rw [ht i x,norm_mul,Real.norm_of_nonneg (hh i)]; apply mul_le_mul_of_nonneg_right _ (hh i); have hV: ‖f i x‖^2=(f i x)^2:=(by rw [← norm_pow,Real.norm_of_nonneg (by positivity)]); nlinarith [sq_nonneg (1- ‖f i x‖)]
   refine ⟨g,⟨⟨v+v,add_nonneg hv hv,fun i x=>?_⟩,fun i=>?_⟩,hx⟩; swap
   · have hv:Bond (f i):=by convert! Bond.scale ((s i)⁻¹) (h.zon i) using 1; funext x; change _=(s i)⁻¹*p i x; unfold f; rw [div_eq_mul_inv,mul_comm]
     exact (Bond.keep 1|>.add (hv.pow _)).mul (Bond.keep _)
   rw [Real.norm_of_nonneg ((norm_nonneg _).trans (hx i x))]; unfold care; let a:=t i x; have h₁:(1:ℝ) ≤ a:=one_le_pow₀ (by simp); have h₂:(f i x)^2≤ a^2:=by rw [← Real.norm_of_nonneg (by positivity :0 ≤ (f i x)^2),norm_pow]; gcongr; exact hl i x
   apply le_trans (mul_le_mul_of_nonneg_right (show 1+ (f i x)^2 ≤ a^2+a^2 from by nlinarith only [h₁,h₂]) (hh i)); rw [pow_add]; unfold a t s;exact le_of_eq (by ring)
lemma Wash {p q:W→ℝ}{s:W→Side}(h:Cash s k q p): Cash s k q (fun i=>‖p i‖):= by obtain ⟨c,hc,H⟩:=h; exact ⟨c,hc,fun i=>by simpa using H i⟩
variable (n:W→Side)(H:∀ i,Even (n i).val)(Y:∀ i,Plot (H i))
local notation "C'" i=> Libra.Keys G (Stand.Free (Y i))
-- budget ≥4
variable {v v' b b':W→ℝ}(A:(j:W)→Alps K T i (v j))(Z:(l:W)→Alps K T j (v' l))
variable (L:∀ i,Bor (H i) (A i) (b i))(V:∀ i,Bor (H i) (Z i) (b' i))
variable {q s:W→ℝ}
abbrev vL(p:W):= penon ((L p).L (Y p))
local notation "AΞ"=>vL n H Y A L
local notation "DΞ"=>vL n H Y Z V
local notation "Wµ" i=>Chart.tangent G (Stand.Free (Y i))
local notation "B₁"=>fun i=> Law.average (AΞ  i) (Wµ i)
local notation "B₂"=>fun i=> Law.average (DΞ  i) (Wµ i)
lemma RushV {u w:ℕ}(ht:4≤ i)(hk:4≤ j)(hs:G.Simple)(hz:WindZ n r u q (fun i=> Impact (AΞ  i) (DΞ  i)))(hp:0 ≤ q)(hv:0 ≤ s)(f:(i:W)→ (C' i)→ ℝ)(hh:WindZ n e w s f):
   Cash n (8+(r+e)+4*(u+w+(u+w))) (q*s) (fun i=> (B₁) i (f i)-(B₂) i (f i)):=by
      let g(i):= Impact (AΞ  i) (DΞ  i); obtain ⟨t,h,h'⟩:= WindZ.BoostF g hz hp; obtain ⟨x,hx,hX⟩:= WindZ.BoostF (g*f) (hz.mul hh hp) (fun i=> mul_nonneg (hp i) (hv i)); let Q:=q*s; have hQ:0 ≤ Q:=fun i=>mul_nonneg (hp i) (hv i); let D:= 8+(r+e)+4*(u+w+(u+w)); let p(i):=‖(B₁) i (x i)‖+‖(B₂) i (x i)‖; let a(i):=‖(B₁) i (t i)‖ + ‖(B₂) i (t i)‖; let v(i):=‖(B₁) i (f i)‖+ ‖(B₂) i (f i)‖
      have hz:Cash n (4+(r+e)+4*(u+w+(u+w))) Q p:= gold_plus (Wash (wages A n H Y L x hx hQ ht hs)) (Wash (wages Z n H Y V x hx hQ hk hs)); have he: Cash n (4+r+4*(u+u)) q a:= gold_plus (Wash (wages A n H Y L t h hp ht hs)) (Wash (wages Z n H Y V t h hp hk hs)); have hh': Cash n (4+e+4*w) s v:=gold_plus (Wash (wages A n H Y L f hh hv ht hs)) (Wash (wages Z n H Y V f hh hv hk hs))
      obtain ⟨c,hc,H⟩:=gold_plus (costGauge n hz hQ le_rfl (show 4+(r+e)+4*(u+w+(u+w)) ≤ D by unfold D;omega)) (costGauge n (gold_times he hp hh') hQ le_rfl (show 4+r+4*(u+u)+(4+e+4*w) ≤ D from by unfold D;omega)); refine ⟨c,hc,fun i=> ?_⟩
      apply (swollen (Wµ i) (AΞ  i) (DΞ  i) (f i) (x i) (t i) (hh.zon _) (hx.zon _) (h.zon _) (fun j=> (by rw [mul_comm];exact hX i j)) (h' i)).trans; exact (le_abs_self ((p+a*v) i)|>.trans (H i))
end YM.OPE.Quit.PriceZ
