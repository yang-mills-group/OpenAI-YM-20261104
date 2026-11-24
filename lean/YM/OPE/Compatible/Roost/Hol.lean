import YM.OPE.Compatible.Roost.Riders
/-!
# frame power optics. Arbitrary Hop reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b u:ℝ}(A:Alps K T i v){D:Alps K T j v'} {U:Boxes G P' K.K}
local notation "Y!"=>solar G d τ
local notation "T!"=> Tracts G d τ
open JetS
variable {H:LocalRatio R}{hs:G.Simple}{X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}
lemma wider (q:ℕ)(he:P'.L=P.L^m): CountL c P.L (q+m)=CountL c P.L q*P'.L :=by simp only [staysX (P:=P),Prairies.stageN]; rw [pow_add,he,mul_assoc]
lemma telV (q:ℕ)(he:P'.L=P.L^m)(x:Site c) : HEq (spikeS K P x (q+m)) ((χ' (K:=K) (CountL c P.L q) P').embed (spikeS K P x q)):=by
       rw [←wrap_lift x]; let R:=χ' (K:=K) (CountL c P.L q) P'; rw [changedH (P:=P),changedH (P:=P), Ratio.embed_wrap]; have h: R.count=P.L^m:=he; rw [show R.count=P.L^m from h]; simp only [Prairies.rangeS,Prairies.ζ, pow_add, PNat.mul_coe]; rw [Nat.mul_comm (↑(P.L^q):ℕ),mul_smul]; let y:Side:=CountL c P.L (q+m); have h(c n:Side)(ht:c=n)(p:Cover):HEq (wrap c p) (wrap n p):=by subst n;rfl
       exact h _ _ (wider _ he) _
lemma HouseHE (x y:Site c)(p q:Site f)(K:Even c.val)(he:c=f)(U:Even f.val) (hp:HEq x p)(hh:HEq y q)(hs:G.Simple)(h:4 ≤ i)(hr:LocalRatio R)(hz:0 ≤ v)(t:Phase): ArmZ A x y K hs h hr hz (d:=d) (τ:=τ) t=ArmZ A p q U hs h hr hz (d:=d) (τ:=τ) t:=by
     subst f; cases hp; cases hh;rfl
variable (H hs) (t:Town A D U R u)(h: Aware d τ) (hi:4 ≤ i)(hj:4 ≤ j)(ha:0 ≤ v)(hb:0 ≤ v')
lemma raising (V: Even c.val)(x y:Site c)(p q:solar G d τ)(i:Phase)(a:Axis)(r:ℕ)(he:P'.L=P.L^m): Variance.HillP A H hi hs ha P x y V a i (r+m) p q= (Plume (fun _:Unit=> even_both (χ' (K:=K) (CountL c P.L r) P') (evenBoot K P V r)) (fun _=>A) (fun _=> (χ' (K:=K) _ P').embed (spikeS K P x r)) (fun _=>(χ' (K:=K) _ P').embed (spikeS K P y r)) hs hi H (fun _=>ha) i) () (spose a G d τ p) q :=by
     let M:=χ' (K:=K) (CountL c P.L r) P'; have hv:=HouseHE A (spikeS K P x (r+m)) (spikeS K P y (r+m)) (M.embed (spikeS K P x r)) (M.embed (spikeS K P y r)) (evenBoot K P V (r+m)) (wider _ he) (even_both M (evenBoot K P V _)) (telV (K:=K) _ he x) (telV (K:=K) _ he y) hs hi H ha (τ:=τ) (d:=d) i; exact congr_arg (fun p'=> (p':Dice (solar G d τ)) (spose a G d τ p) q) hv
end YM.OPE.Stroke
