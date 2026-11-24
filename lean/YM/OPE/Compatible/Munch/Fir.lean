import YM.OPE.Compatible.Munch.Air
/-! # independent W chart. ∆ cost with ℓ weights, arbitrary F. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m Z:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f){q:Sender L}
variable {B: Law (Bid.Dir G L.c)}(μ:Measure (Bid.Dir G L.c))[μ.IsAddHaarMeasure] {X:Seats L.ForestQ}
variable {N: ChartRatio G}(hN:LocalRatio N)
variable (hp:Funded L X q a k)
include hp hN
lemma R_status : Status (GPY L q N):=by
        let p (x:L.DirA):= q x.2; let H:=L.F.L
        refine SaltV (I:=(forest _ L.H).Free) H N hN p (statusF (statusF (p:=q) ?_ (ContinuousLinearMap.snd ℝ (Bid.Dir G L.c) (AxisChart G L.ForestQ))) (Fiber.drape _ _ H.M).toContinuousLinearMap); intro i; change Stature (fun x=>(q x).seq i.val) 0; refine statureBase (Funded.strong _ _ hp i) ⟨‖a‖,k,norm_nonneg _,fun x=>?_⟩; exact (Funded.norm _ _ hp x le_rfl i).trans (mul_le_mul_of_nonneg_right (Real.le_norm_self _) (pow_nonneg (by positivity) k))
variable (H:StackP N r R β)
set_option quotPrecheck false
local notation "W'"=> Bid.Dir G L.c
local notation "χ"=> wallet3 G k s c v u C
local notation "g!"=> Gov s u
local notation "Π!"=> quart B μ
variable (η:Phase)(hs:G.Simple)(hw:L.b=0)(h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:0≤v)(hX:(X.card:ℝ) ≤ z)(hφ:PerSeat (L:=L) B A)(hA:0≤A)
variable (hS:∀ t z a:ℝ,‖wallet3 G k s c v u C t z a β‖≤ D*(1+(‖t‖+(‖z‖+‖a‖)))^Z)(hD:0≤ D)
noncomputable abbrev Ωθ (z a:ℝ)(k:ℕ) := (1+(‖z‖+‖a‖))^k
noncomputable abbrev Ywall (ε z a:ℝ)(D:ℝ)(k m:ℕ) := burst ε m*D*Ωθ z a k
noncomputable abbrev lamp_B (G:Gauge)(k n:ℕ)(R:ℝ):price:=hikeP (J1+crownG G (n+1) R) k
abbrev Censor (L:Host K T)(q:Sender L)(N:ChartRatio G)(η:Phase)(x: Site L.f)(i:ℕ): Bid.Dir G L.c→ℝ:= (skry (GPY L q N) η) ∘ Qspot L x i
include H hs hw h ht hc he hv hX hφ hA hS hD
lemma pineM (i:ℕ)(hK:Training L x X i): Cane (quart B μ) (Censor L q N η x i-Censor L q N η x (i+1)) (Ywall (Gov s u) z a D Z i • lamp_B G Z i A):=by
         let f:=Qspot L x i; let g:=Qspot L x (i+1); let U(w:W'):=‖g w‖; let T:= Ywall g! z a D Z i; have hy:0 ≤ Ωθ z a Z:=by unfold Ωθ; positivity
         have hz':0 ≤ burst g! i:= Real.exp_nonneg _; have hT:0 ≤T:=mul_nonneg (mul_nonneg hz' hD) hy
         let Y:= Censor L q N η x
         have hf : ∀ w:W', ‖Y i w-Y (i+1) w‖≤ T*(1+U w)^Z:=by
               intro w; let F:= f w; let W:= g w; let S:= worldA L F; have hY : ‖g w‖≤ U w:= le_rfl; change ‖(GPY L q N (f w)).seq _ - (GPY L q N (g w)).seq _‖ ≤ _
               have heP: Scale S (U w):= grantW (foothQ x w i.le_succ); rw [tradeV hN L q h hw hs,tradeV hN L q h hw hs]; apply (refunds x hN H h ht hc he hv heP hY (Reap_Q x w i.le_succ) hX hK hp (Nat.cast_nonneg _) η).trans; let S':= (1+(‖z‖+‖a‖)); let V:=U w; have hU:0≤V:=norm_nonneg _
               have hz:(1+(‖V‖+(‖z‖+‖a‖)))≤ S'*(1+ V):=by unfold S'; rw[Real.norm_eq_abs V, abs_of_nonneg hU]; nlinarith only [mul_nonneg hU (norm_nonneg z),mul_nonneg hU (norm_nonneg a)]
               have he':χ V z a β≤D*(S'^Z*(1+V)^Z):= by rw[←mul_pow]; exact ((Real.le_norm_self _).trans (hS ..)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hz _) hD)
               apply (mul_le_mul_of_nonneg_right he' hz').trans_eq; unfold T Ywall Ωθ S' V;ring
         have hL(i:ℕ):Continuous (Y i):= (R_status hN hp η).smooth.continuous.comp (Qspot L x i).continuous
         let P:= ((Cane.constant (μ:=quart B μ) (1:ℝ) (show ‖(1:ℝ)‖≤1 by norm_num)).add ((mac x B μ hφ hA (i+1)).normVal)) -- mac uses A explicit. fix
         let E := Cane.scal (powerQ P Z) T; refine (of_K E ((hL i).sub (hL (i+1))).aestronglyMeasurable ?_).grow ?_
         · intro w; exact (hf w).trans (Real.le_norm_self _) -- Pi smul issues
         intro j _; rw [Real.norm_eq_abs T, abs_of_nonneg hT]
end
end YM.OPE.Borealis.Galea
