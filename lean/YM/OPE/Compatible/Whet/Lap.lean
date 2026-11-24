import YM.OPE.Compatible.Whet.Reeds
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
variable (n:W→Side)(H:∀ i,Even (n i).val)(Y:∀ i,Plot (H i))
local notation "C'" i=> Libra.Keys G (Stand.Free (Y i))
-- budget ≥4
variable {v v' b b':W→ℝ}(A:(j:W)→Alps K T i (v j))(Z:(l:W)→Alps K T j (v' l))
variable (L:∀ i,Bor (H i) (A i) (b i))(V:∀ i,Bor (H i) (Z i) (b' i))
variable {q s:W→ℝ}
local notation "AΞ"=>vL n H Y A L
local notation "DΞ"=>vL n H Y Z V
local notation "Wµ" i=>Chart.tangent G (Stand.Free (Y i))
structure Foam {v:W→ℝ}(A:(j:W)→ Alps K T i (v j)):Prop where
 coast : ∃ p:Clip, ∀ i, (A i).clip=p
 cap : ∃ c:ℝ,0 ≤ c∧∀ i,v i ≤ c
 bill : 0 ≤ v
structure Linking (_A:(j:W)→Alps K T i (v j)) (Z:(l:W)→Alps K T j (v' l))(s:W→ℝ):Prop where
    arc: Foam _A
    b:Foam Z
    serv:0 ≤ s
    germ₂:ToughZ (fun i=>(_A i).word 2- (Z i).word 2) s
    germ₃:ToughZ (fun i=>(_A i).word 3- (Z i).word 3) s
    germ₄:ToughZ (fun i=>(_A i).word 4- (Z i).word 4) s
    germY:ToughZ (fun i=>(_A i).liftZ 2- (Z i).liftZ 2) s
-- stand.Head
lemma hTHat (hs:G.Simple)(hr:LocalRatio R)(hz:b=0)(hh:Foam A):WindT n 8 6 1 (fun i=> ((L i).L (Y i)).hat R) :=by
   obtain ⟨p,h⟩:= hh.coast; obtain ⟨c,hT,hZ⟩:=hh.cap; refine BootPrice A n H Y R hr 0 c _ L ?_ hh.bill hZ hT h hs; intro i; rw [hz,Pi.zero_apply,abs_zero]
local notation "W'" i=>Chart.tangent G (Stand.Free (Y i))
lemma glowV (x y:W→solar G d τ)(a b':(i:W)→Site (n i))(hs:G.Simple)(hr:LocalRatio R)(ht:4 ≤ i)(hz:b=0)(hh:Foam A): Permit n (4+(0+8)+4*((d+2+(d+2))+6)+(4+8+4*6+(4+8+4*6))) (fun i=>‖x i‖*‖y i‖) (fun i=> RGram (H i) (Y i) (L i) (x i) (y i) (a i) (b' i) R):=by
     let f(i):= ((L i).L (Y i)).hat R
     let p(i):= isolate (H i) (Y i) (x i).val (y i).val (a i) (b' i)
     rw [show (fun i=>RGram (H i) (Y i) (L i) (x i) (y i) (a i) (b' i) R)=(fun i=> fair (W' i) (AΞ i) (f i) (p i)) from funext fun i=>Lid.cutOut ((L i).L (Y i)) hr _ _ (penon_shape _)]
     exact channelP A n H Y L (dualWorld x y n H Y a b') (fun i=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun i z=>Lid.hat_full ((L i).L (Y i)) hr z) (hTHat n H Y A L hs hr hz hh) ht hs
lemma GramD (x y:W→solar G d τ)(a c:(i:W)→Site (n i))(hs:G.Simple)(hr:LocalRatio R)(hp:4 ≤ i)(ht:4 ≤ j)(he:b=0)(he':b'=0)(hh:Linking A Z s):
     Permit n (payV 4 2 (d+2+(d+2))) (s*(fun i=>‖x i‖ * ‖y i‖)) (fun i=> RGram (H i) (Y i) (L i) (x i) (y i) (a i) (c i) R-RGram (H i) (Y i) (V i) (x i) (y i) (a i) (c i) R):=by
         unfold RGram; simp_rw [fun v=>Lid.cutOut ((L v).L (Y v)) hr _ (isolate (H v) (Y v) (x v).val (y v).val (a v) (c v)) (penon_shape _),fun v=> Lid.cutOut ((V v).L (Y v)) hr _ (isolate (H v) (Y v) (x v).val (y v).val (a v) (c v)) (penon_shape _)] -- underscore inference
         obtain ⟨p,h⟩:=hh.arc.coast; obtain ⟨f,h'⟩:= hh.b.coast; refine channelD n H Y A Z L V _ (hTHat n H Y A L hs hr he hh.arc) (hTHat n H Y Z V hs hr he' hh.b) (fun i=> Lid.hat_full ((L i).L (Y i)) hr) (fun i=> Lid.hat_full ((V i).L (Y i)) hr) (topSkin n H Y A Z L V hh.serv hh.germ₂) hh.serv (BoolHat n H Y A Z L V h h' hs hr he he' hh.serv hh.germ₃ hh.germ₄ hh.germY) (dualWorld x y n H Y a c) (fun i=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) hp ht hs
end YM.OPE.Quit.PriceZ
