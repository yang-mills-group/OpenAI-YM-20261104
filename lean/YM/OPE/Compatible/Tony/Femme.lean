import YM.OPE.Compatible.Tony.Baba
/-!
# Extending a chamber estimate from a tail of the sequence

`Visionτ` requires the `VisionTag` bound for every comparison satisfying `IceD`.
`lift_crop` extends a `CropFill` witness from a tail to the full sequence.
`Visionτ.Wish` uses this extension to obtain `PassportIce` for sequences whose
scales tend to infinity and whose periods meet the `Ramp` threshold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
open GlowPack Silt.Phere Ibis Owl Lass Lass.Zest Spells Yolk Pill Dial Merchant Merchant.Sleeve
variable {L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i:ℕ)(he:highStage L hs a V ≤ i)
variable (S:Stage)(X:BankW L hs a V he S.clip) (P:Pad G)
set_option quotPrecheck false
set_option maxHeartbeats 200000
local notation "F*"=> solar G (l+6+6) V.pay.st.τ
variable {n:ℕ→Side}{β:ℕ→ℝ} {ξ:ℝ}{r:ℕ}
variable (A:∀ j, HillZ (T:=T) S i r l ξ (β j) (n j))
variable (g:ℂ→L[ℝ]ℝ)
open Next.Scheduling CardinalQ
variable (ht:Tendsto β atTop atTop)(hp:∀ j,RichHill i S (A j))
noncomputable abbrev VisionTag (x:ℕ→ solar G (l+6+6) (V.pay.st.τ)):= Audible G K.K n atTop (Counters β) i (l+6) (fun j=>(A j).lens.ℳ.gear) (hazard V he) (fun j=> Aview (portrait V i he S P (A j) g -x j) 0 (Clock.gap (A j).path.beta)) q1
-- Require the observed difference estimate for every admissible chamber comparison.
structure Visionτ (h:G.Simple)(a:Axis):Prop where
       needs :∀ (K:Sponsor G)(T:Seasons K) (H:LocalRatio (chart G))(L:PriceBook H T)(l:ℕ)(V:Foyer L h a l (l+6+6))(i:ℕ)(he:highStage L h a V ≤ i)(S:Stage)(_X:BankW L h a V he S.clip)(P:Pad G) (r:ℕ)(t:ℝ)(β:ℕ→ℝ)(n:ℕ→Side), Tendsto β atTop atTop →(∀ j,Ramp V i he (β j) ≤ (n j).val) →∀ (A:(j:ℕ)→ HillZ (T:=T) S i r l t (β j) (n j)), ∀ (U:Scaffold atTop (Counters β) n (Mnd i S A) r) (g:ℂ→L[ℝ]ℝ)(x:ℕ→solar G (l+6+6) V.pay.st.τ)(z:ℕ→Law (Chamber G r))(U' R':Forge G n), IceD V i he S P A g U z x U' R'→ VisionTag V i he S P A g x
-- Eventual estimates on a tail extend to the full sequence.
lemma tommy (m:ℕ)(p:ℕ→Prop) (h:∀ᶠ i:ℕ in atTop,p (m+i)): ∀ᶠ i:ℕ in atTop,p i:=by
       obtain ⟨j,hj⟩:=eventually_atTop.mp h; refine (eventually_ge_atTop (m+j)).mono (fun i hi=>?_ ); have he:m+(i-m)=i:=(by omega); have hx:= hj (i-m) (by omega); rwa[he] at hx
lemma PriceFrom (p:ℕ→ℝ)(c:ℕ→ℝ)(a:ℝ)(Q:ℕ→ ℝ)(h:RateLE atTop (fun i=>c (m+i)) Q a)(hp:∀ᶠ i:ℕ in atTop,p (m+i)= Q i):RateLE atTop c p a:= by intro r hr; refine tommy m _ ?_; filter_upwards [hp,h r hr] with i hi ht; rw[hi];exact ht
lemma lift_crop (m:ℕ) (h:CropFill V i he S P (fun j=>A (m+j)) g (n:=fun j=>n (m+j)) (β:=fun j=>β (m+j)) (φ:=atTop)): CropFill V i he S P A g (φ:=atTop):=by
       let σ(i:ℕ):=m+i; obtain ⟨f,hf,h,H⟩:=h.fills; let X(i):=f (i-m); have hx(i):X (m+i)=f i:=(by simp [X]); refine ⟨X,?_ ,tommy m _ ?_,?_⟩
       · intro k; obtain ⟨b,hb,Q⟩:=hf k; let B (n:ℕ):=b (n-m); have he(i:ℕ): B (m+i)=b i:=(by simp [B]); exact ⟨B,PriceFrom B (Counters β) 0 b hb (Eventually.of_forall he), tommy m _ (Q.mono fun i hi=>by rw [he,hx i]; exact hi)⟩
       · filter_upwards [h] with i hi;rw[hx i];exact hi
       obtain ⟨r,hr,H⟩:= H.yod; let p(i:ℕ):= r (i-m); have he(i:ℕ): p (m+i)=r i:=(by simp [p]); refine ⟨p,PriceFrom p (Counters β) _ r hr (Eventually.of_forall he),tommy m _ ?_⟩; filter_upwards [H] with i hi; rw [he,hx i]; exact hi
lemma Visionτ.Wish {G:Gauge}{h:G.Simple}{a}(q:Visionτ h a):PassportIce a h:=⟨fun K T H L l V i he S X P r t β n ht hh A g=>by
       obtain ⟨M,hM⟩:= eventually_atTop.mp (hill_forecast V _ he S A ht hh); have hμ:Tendsto (fun i=>β (M+i)) atTop atTop:=ht.comp (tendsto_atTop_mono (fun (i:ℕ)=>Nat.le_add_left i M) tendsto_id); let C (j:ℕ):=A (M+j); let a(i:ℕ):=n (M+i); let b(i:ℕ):=β (M+i); have hu : Scaffold atTop (Counters b) a (Mnd i S C) r:= hillFresh i S (r:=r) C hμ fun i=> hM _ (by omega); obtain ⟨z,x,y,V',hX⟩:= avail V i he S P (n:=a) (r:=r) C g hμ hu; apply lift_crop V i he S P A g M
       exact ⟨x,hX.seed.manned.prepaid.life,Eventually.of_forall (fun i=> hX.seed.manned.prepaid.spirit i),q.needs K T H L l V i he S X P r t b a hμ (fun i=>hh _) C _ g x z y V' hX⟩⟩
end YM.OPE.Stroke
