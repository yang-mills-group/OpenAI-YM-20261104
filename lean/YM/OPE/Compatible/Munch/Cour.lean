import YM.OPE.Compatible.Munch.Fashion
/-! # magnitude budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f){q:Sender L}{Y:Studio L}
variable (j':Phase)(h:L.Rich s c e v u C)(ht:0<s)(hc:0≤c)(he:0<e)(hv:Scale Y t) {X:Seats L.ForestQ}(hx:(X.card:ℝ)≤ z)(hX:Training L x X M)(hp:Funded L X q a k)
variable {f:L.DirA→ℝ}
noncomputable abbrev RtM (n:ℕ):ℝ:=Push.AbsoluteSums.Animals.ballCost (16*n)
noncomputable abbrev UsZ (G:Gauge)(n:ℕ)(s u J:ℝ):ℝ:= tokenCost G n (Gov s u)+J*ΛGram G (Gov s u)^n
noncomputable abbrev Cave2(G:Gauge)(k n:ℕ)(s c u C t z a J r:ℝ):= (r*‖Dig2 G k n s c u C t z a‖)* UsZ G n s u J
noncomputable abbrev Cave3(G:Gauge)(k n:ℕ)(s c u C t z a J r:ℝ):= ((r*r)*‖Dig3 G k n n s c u C t z a‖)*(UsZ G n s u J)*(UsZ G n s u J)
include h ht hc he hv hx hX hp
local notation "μ'"=> Gov s u
lemma Cue2 (hP:Tires L f n A s): ‖Push2 L q Y j' f‖ ≤ Cave2 G k n s c u C t z a (RtM M) A:=by
       obtain ⟨b,hP⟩:=hP
       rw [show Push2 L q Y j' f=∑ z,∑ x:RodZ L n,b z x* Wish2 L q Y j' x from coinX L Y h he ht hc hP ((Quala L Y h he ht hc X hp).Γ j')]; exact Dugout x _ (fun p z=>R2 x j' h ht hc he hv hx hX hp z p rfl hP.pos (hP.dock p z)) (mul_nonneg hP.pos (norm_nonneg _)) (Gov_price ht h.vein.warmth).1
lemma Cue3(hP:Tires L f n A s): ‖Push3 L q Y j' f f‖ ≤ Cave3 G k n s c u C t z a (RtM M) A :=by
       obtain ⟨b,hP⟩:=hP; let T:= A*A*‖Dig3 G k n n s c u C t z a‖; let F(u:Site L.f)(i:RodZ L n):= ticPay x u i M μ'; let Z:= jigB G n M μ'; have hv':0 < μ':= (Gov_price ht h.vein.warmth).1; have hf(u i):0 ≤ F u i:=add_nonneg (wake ..) (unt_J ..); have hZ:0≤Z:= (sum_nonneg fun _ _=>sum_nonneg fun _ _=>hf ..).trans (Jig x hv' n M); have hT:0≤T:=mul_nonneg (mul_nonneg hP.pos hP.pos) (norm_nonneg _); let w(u i p j):=b u i*b p j* Wish3 L q Y j' i j; have hw(c i p j): ‖w c i p j‖ ≤ (T*F c i)*F p j:=by
              rw [_root_.mul_assoc]; apply R3 x j' h ht hc he hv hx hX hp i c j p rfl (mul_nonneg hP.pos hP.pos); rw[norm_mul,mul_add,neg_add,Real.exp_add,mul_mul_mul_comm A]; exact mul_le_mul (hP.dock c i) (hP.dock p j) (norm_nonneg _) (mul_nonneg hP.pos (Real.exp_nonneg _))
       rw [show Push3 L q Y j' f f =∑ c,∑ i,∑ j,∑ k,w c i j k from EarthX L Y h he ht hc hP hP ((Quala L Y h he ht hc X hp).Γ j')]; exact Dugout (n:=n) x _ (a:=T*Z) (fun c i=> (Dugout x _ (hw c i) (mul_nonneg hT (hf c i)) hv').trans_eq (mul_right_comm T (F c i) Z)) (mul_nonneg hT hZ) hv'
noncomputable abbrev Caver(G:Gauge)(k:ℕ)(s c v u C t z a J β:ℝ) := ‖RiseT G k s c u C t z a 1‖+(‖Cave2 G k 4 s c u C t z a J c‖ + ‖Cave2 G k 2 s c u C t z a J (v+4*β)‖)+‖Cave2 G k 3 s c u C t z a J c‖ + ‖Cave3 G k 3 s c u C t z a J c‖
omit h ht hc he hv hx hX hp in
private lemma Dp {a b c d:ℝ}(h:‖a‖≤c)(he:‖b‖≤ d): ‖a+b‖ ≤ c+d:=(norm_add_le ..).trans (add_le_add h he)
variable {N:ChartRatio G}(hN:LocalRatio N)(H:StackP N r R β)(hu:0≤ v)
include hN H hu
lemma SΔ : ‖(MuseY L q N Y).seq j'.val‖ ≤ Caver G k s c v u C t z a (RtM M) β:=by
         let Z:= Caver G k s c v u C t z a (RtM M) β; let U:= ‖RiseT G k s c u C t z a 1‖; let A:= ‖Cave2 G k 3 s c u C t z a (RtM M) c‖
         have hp' : U+A ≤ Z:=by unfold Z Caver U A; linarith only [norm_nonneg (Cave2 G k 4 s c u C t z a (RtM M) c),norm_nonneg (Cave2 G k 2 s c u C t z a (RtM M) (v+4*β)), norm_nonneg (Cave3 G k 3 s c u C t z a (RtM M) c)]
         obtain ⟨hψ,hψ'⟩:= leafE L h he hc; have hg(j:Phase): ‖Push2 L q Y j (Rate3 L)‖ ≤ A:= (Cue2 x j h ht hc he hv hx hX hp hψ).trans (Real.le_norm_self _); have hA(j:Phase): ‖a_ Y.μφ (Spex L Y q j)‖ ≤ U:= ((Fans h ht hc he hv X hx q hp j).Integral).trans (Real.le_norm_self _); rw[BitsG L Y hN H h he ht hc hu q X hp]; fin_cases j'
         · exact (hA 0).trans ((le_add_of_nonneg_right (show 0 ≤A from norm_nonneg _)).trans hp')
         · exact (Dp (hA 1) (hg 0)).trans hp'
         refine Dp (Dp (Dp (hA 2) (Dp ((Cue2 x 0 h ht hc he hv hx hX hp hψ').trans (Real.le_norm_self _)) ((Cue2 x 0 h ht hc he hv hx hX hp (taper L hN H h he hu)).trans (Real.le_norm_self _)))) (hg 1)) ?_; rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans ((Cue3 x 0 h ht hc he hv hx hX hp hψ).trans (Real.le_norm_self _))
end
end YM.OPE.Borealis.Galea
