import YM.OPE.Compatible.Karls.Elm
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
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
section funds
variable {W:Type}{ν:W→Side}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
abbrev NPay (ν:W→Side)(p:W→E)(k:ℕ)(q:W→ℝ):=Cash ν k q (norm ∘ p)
lemma bundleP {p:W→E}{q:W→ℝ} : NPay ν p k q ↔ ∃ a:ℝ,0 ≤ a∧∀ i:W, ‖p i‖≤ a*((ν i).val:ℝ)^k*q i:=by simp only [NPay,Cash,Function.comp_apply,norm_norm]
lemma constantV (n:W→Side)(c:E): NPay n (fun _:W=>c) k 1:=by refine bundleP.2 ⟨‖c‖,norm_nonneg _,fun i=> ?_⟩; rw [Pi.one_apply,mul_one]; exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (W_le _))
lemma Lpay {p t:W→E}{q:W→ℝ}(h:NPay ν p k q)(hv:NPay ν t k q): NPay ν (p+t) k q:=by
    obtain ⟨a,hA,b⟩:=bundleP.mp h; obtain ⟨c,hc,H⟩:=bundleP.mp hv; exact bundleP.mpr ⟨a+c,add_nonneg hA hc,fun i=> by rw [add_mul,add_mul]; exact (norm_add_le ..).trans (add_le_add (b i) (H i))⟩
lemma FarCap {p:W→F}{q:W→E} [NormedAddCommGroup Q]{z:W→Q}{t s:W→ℝ}(h:NPay ν p k s)(hv:NPay ν q l t)(hs:0 ≤ s)(he:∀ i,‖z i‖≤ ‖p i‖*‖q i‖) :NPay ν z (k+l) (s*t):=by
     obtain ⟨a,A,B⟩:=bundleP.1 h; obtain ⟨b,D,H⟩:=bundleP.1 hv; refine bundleP.2 ⟨a*b,mul_nonneg A D,fun i=>?_ ⟩; have hx:0 ≤ s i:=hs i; exact (he _).trans ((mul_le_mul (B i) (H i) (norm_nonneg _) (by positivity)).trans_eq (by rw [pow_add,Pi.mul_apply]; ring))
variable [NormedSpace ℝ E][NormedSpace ℝ F]
lemma flyP {a b:W→ E→L[ℝ] F}{K:W→ Dice F}{p q t:W→ℝ}(ha:NPay ν a k p)(hb:NPay ν b i q)(hp:0 ≤ t)(hq:0 ≤ p)(hk:NPay ν K j t): NPay ν (fun i=>rollD (a i) (b i) (K i)) (j+k+i) (t*p*q):=by
     obtain ⟨c,hc,H⟩:=bundleP.1 ha; obtain ⟨d,hd,D⟩:=bundleP.1 hb; obtain ⟨B,hB,V⟩:=bundleP.1 hk; refine bundleP.2 ⟨B*c*d,by positivity,fun i=>?_⟩; have ht:0 ≤ t i:=hp i; have hx:0 ≤ p i:=hq i; apply (segment (a i) (b i) (K i)).trans; apply le_trans (mul_le_mul (mul_le_mul (V i) (H i) (norm_nonneg _) (by positivity)) (D i) (norm_nonneg _) (by positivity)); simp only [pow_add,Pi.mul_apply]; exact le_of_eq (by ring)
end funds
section push
variable {u:ℝ}{A:Alps K T i v}{D:Alps K T j v'}{τ:Phase→ℕ}
local notation "Y!"=> solar G d τ
variable (hS:G.Simple)(hp:LocalRatio R)(hq:Aware d τ)
variable (s:Axis)
-- reflection marker, either input. Gram use half inner later.
noncomputable def spose (a:Axis)(G:Gauge)(d:ℕ)(τ: Phase→ℕ): solar G d τ →L[ℝ] solar G d τ :=
    (Mirror a G d τ ∘L (solar G d τ).subtypeL).codRestrict _ (fun x=>solarMirror a x.val x.property)
lemma sun_marks (h:Town A D U R u)(p:Y!): yankV D h hp hS hq (spose s G d τ p)= spose s G d τ (yankV D h hp hS hq p):=by
    apply Subtype.ext; change rebase G hq (-u) (actor A U R 0 _ hq (Mirror _ _ _ _ p.val))=Mirror _ _ _ _ (rebase G hq (-u) (actor A U R 0 _ hq _)); rw [show actor _ _ _ _ _ _ _= _ from interposes (b:=0) s A P U ⟨hS,hp,h.eph⟩ hq p]; exact vivid ..
end push
end YM.OPE.Quit.PriceZ
