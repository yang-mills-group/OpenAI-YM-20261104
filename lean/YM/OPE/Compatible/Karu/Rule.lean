import YM.OPE.Compatible.Karu.Told
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
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
variable (Y Z:(solar G d τ)→L[ℝ] (solar G d τ))(hp:LocalRatio R)(hq:Aware d τ)(he:Crest G P K.K m)(hs:G.Simple)
variable {W:Type}(f:W→ TileC T P p R b)(c₁:ℝ)(hh:∀ i,upperX (f i)≤c₁){n: W→Side}(H:∀ i,Even (n i).val)(x y:(i:W)→ Site (n i))(ψ:Phase)
abbrev PeakA (U:Alps K T i v)(hi:4 ≤ i)(ha:Aware d τ):= (Fallix G ha K U.gear hi).toContinuousLinearMap
noncomputable def ZoneA (U:Alps K T i v)(hi:4 ≤ i)(h:0 ≤ v)(L:Side)(V:Even L.val)(x y:Site L)(j:Phase): Dice (Tracts G d τ):= rollD (Y ∘L PeakA U hi hq) (Z ∘L PeakA U hi hq) (ArmZ U x y V hs hi hp h j)
abbrev LA (p: TileC T P p R b):= PeakA (UA p) P.order_cut hq
abbrev LE (p:TileC T P p R b):= PeakA (VA p) P.order_cut hq
include he
lemma LA_charge : Brim (LA (p:=p) (b:=b) hq) (LE hq) (upperX (P:=P) (H:=T) (V:=R)) fareI:=by
     have hL:= saucy (b:=b) (R:=R) (p:=p) (T:=T) he hq (-(1/2:ℝ)); have hx:1 ≤ (upperX:TileC T P p R b→ ℝ):= max_cap _ _ _ _ _;
     have hv:= (Canal hL (Brim.constant (PoseQ G hq).toContinuousLinearMap) hx fixedTheta); let f(i: TileC T P p R b):=(PoseQ G hq).toContinuousLinearMap ∘L Larix G (UA i).gear P.order_cut K.K hq (-(1/2:ℝ)); let g(i:TileC T P p R b):=(PoseQ G hq).toContinuousLinearMap ∘L Larix G (VA i).gear P.order_cut K.K hq (-(1/2:ℝ)); rw [show LA (P:=P) hq = f from funext fun i=> ContinuousLinearMap.ext fun x=> rfl,show LE (P:=P) hq=g from funext fun i=>ContinuousLinearMap.ext fun x=>rfl];exact hv
include hh
omit he in
lemma consumeP {n:W→Side}[NormedAddCommGroup E] (k:TileC T P p R b→ℝ)(hp:0 ≤ k)(p':TileC T P p R b→ E)(hv:Wealth p' upperX k): NPay n (p'∘f) 0 (k∘f):=by
          obtain ⟨c,hc,l,hv⟩:=hv; refine bundleP.2 ⟨c*(max 0 c₁)^l,by positivity,fun i=>?_⟩; rw [pow_zero,mul_one]; exact (hv _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (max_cap (P:=P) (p:=p) (H:=T) (V:=R) (C:=b) _)) ((hh i).trans (le_max_right ..)) l) hc) (hp (f i)))
omit he in lemma bothP {n:W→Side}[NormedAddCommGroup E](p' g':TileC T P p R b → E)(h: Brim p' g' upperX fareI): NPay n (fun i=> p' (f i)) 0 1 ∧ NPay n (fun i=> g' (f i)) 0 1 ∧ NPay n ((fun i=> p' (f i))-(fun i=>g' (f i))) 0 (fareI∘f):= ⟨consumeP f c₁ hh 1 zero_le_one p' h.A, consumeP f c₁ hh 1 zero_le_one g' h.B,consumeP f c₁ hh _ fixedTheta _ h.D⟩
lemma FitZ {n:W→Side}:NPay n (fun i:W=> LA hq (f i)) 0 1∧ NPay n (fun i:W=> LE hq (f i)) 0 1∧ NPay n ((fun i:W=> LA hq (f i)) - (fun i:W=> LE hq (f i))) 0 (fareI ∘ f):=by -- include hh
     exact bothP f c₁ hh _ _ (LA_charge hq he)
abbrev FstV (a:Sailing T P p R b)(u:ℕ)(X:Side)(h:Even X.val)(x y:Site X)(j:Phase): Dice (Tracts G d τ):= ZoneA Y Z hp hq hs (a.U u) P.order_cut (zero_le_one.trans a.fits) X h x y j
abbrev Pile (T':TileC T P p R b)(x y:Site c)(H:Even c.val)(i:Phase):= FstV Y Z hp hq hs T'.1.1 T'.2 c H x y i
abbrev Pave (T':TileC T P p R b)(x y:Site c)(H:Even c.val)(i:Phase):= FstV Y Z hp hq hs T'.1.2 T'.2 c H x y i
include hp hh hq
lemma Goss : NPay n (fun i=> Pile Y Z hp hq hs (f i) (x i) (y i) (H i) ψ) (Rune d) 1 ∧
    NPay n (fun i=> Pile Y Z hp hq hs (f i) (x i) (y i) (H i) ψ-Pave Y Z hp hq hs (f i) (x i) (y i) (H i) ψ) (max (Rune d) (Dosage d)) (fareI∘f):=by
       let t(i):=LA hq (f i); let u(i):= LE hq (f i); let f':W→ ℝ:=fareI∘f; have hf:0 ≤ f':= fun i=> fixedTheta _; obtain ⟨h₁,h₂,h₃⟩:=FitZ (n:=n) hq he f c₁ hh;
       let A(i):=UA (f i); let D(i):=VA (f i); have ht:=trice f c₁ hh hs hp he; let G:= Plume H A x y hs P.order_cut hp ht.arc.bill ψ (τ:=τ) (d:=d); let B:= Plume H D x y hs P.order_cut hp ht.b.bill ψ (τ:=τ) (d:=d)
       have hG: NPay n G (Rune d) 1:= vaster H A x y hs P.order_cut hp ht.arc.bill _ ht.arc; have hV:NPay n (G-B) (Dosage d) f':= costGauge n (show NPay n (G-B) (Dosage d) (downK ∘ f) from tipA H A x y hs P.order_cut hp ht.arc.bill D ht.b.bill ψ ht P.order_cut) ht.serv (fun i=>thetaL _) le_rfl
       let D(i):=Y ∘L t i; let R(i):=Z ∘L t i; let D'(i):=Y ∘L u i; let R'(i):= Z ∘L u i; let p(i):=rollD (D i) (R i) (G i); let q(i):= rollD (D' i) (R' i) (B i); change NPay n p _ _ ∧ NPay n (p-q) _ _
       exact waxV Y Z t u h₁ h₂ h₃ G B hG hV hf
end YM.OPE.Quit.PriceZ
