import YM.OPE.Compatible.Tips.Hearth
import YM.OPE.Compatible.Rave.Orb
import YM.OPE.Compatible.Karls.Haven
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Hike.Piece
import YM.OPE.Compatible.Karls.Bent
import YM.OPE.Compatible.Karls.York
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
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
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
open Finset
open PriceZ Hark
variable (H:LocalRatio R)(hs:G.Simple)(X:Sailing T P p R b)
variable (B:Medal P G K.K P.J)(h:Aware d τ)
open Hark
variable (X': Tracts G d τ→L[ℝ] Tracts G d τ) {s r' w:ℝ} {d':ℕ}(D:Stern K P τ d' d w)
variable (J': Crown (p:=p) (b:=b) (T:=T) H hs B D X' r' s e)
local notation "μ"=> lapPrice (Patch.L P) e
open Prairies Hark
variable (V:Even n.val)(a:Axis)(hp:Alps.Crest G P K.K m)
open Balsam Nestle StageLight Pert.Full
variable (L:Lance X){t:ℕ→Side}(Ht:∀ i,Even (t i).val)(ht:Ncap t atTop)(h':∀ᶠ i in atTop, Attest G P d k e d' m τ (t i))
include J' L Ht ht h' hp
open scoped ComplexOrder
lemma nut (u:Lingo r' (Quoin hs D B H X))(p':Saga G e (d+(0:Phase).val))(Hp:FairV (seekY X D u.val) p'):
      let y:= lampPO H hs B X D X' J' u
      Tendsto (fun i=> ((K0 H hs X X' D a (Ht i) (wrap _ (skew a)) (wrap _ (Point a)) hp (e:=e) 0 y y):ℂ)) atTop (𝓝 (Maxwell.Free.bond G (incVec 1 (skew a)) (incVec 1 (Point a)) (turnT a p').terra p'.terra)):=by
         exact Light H hs X B X' D J' (spose a G d τ) (ContinuousLinearMap.id ℝ (solar G d τ)) (GuardZ H hs X B D a) (GuardI H hs X B D) hp (a:=u) (b':=u) L (skew a) (Point a) (slanted a) Ht ht h' (turnT a p') p' (roseP a _ _ Hp K) Hp
omit L in lemma bosslim (x:Bead G d' e)(y:Fruition X' (lapPrice P.L e))(he:τord H hs B X' D J' y=x)(S:ℂ)(hv:Tendsto (fun i=> ((K0 H hs X X' D a (Ht i) (wrap _ (skew a)) (wrap _ (Point a)) hp (e:=e) 0 y y):ℂ)) atTop (𝓝 S)):
    Tendsto (fun i=> boss H hs X B X' D J' (Ht i) a hp (wrap (t i) (skew a)) (wrap (t i) (Point a)) x x) atTop (𝓝 S.re):=by
       have ht':= Complex.continuous_re.continuousAt.tendsto.comp hv; refine ht'.congr' ?_; filter_upwards [togetherH (skew a) (Point a) t ht (slanted a) Ht (K:=K) (P:=P),h'] with i h hG; exact (quotaQ H hs X B X' D J' (Ht i) a hp _ _ hG h y y).trans (by rw [he])
lemma barPos (x:Bead G d' e):∃ c:ℝ,(x ∉ Ghost G d' e→0 < c)∧
     Tendsto (fun i=> boss H hs X B X' D J' (Ht i) a hp (wrap (t i) (skew a)) (wrap (t i) (Point a)) x x) atTop (𝓝 c):=by
        obtain ⟨u,hU,p',Hp,hq⟩:= capsuleGlow H hs X B X' D J' L x; let y:= lampPO H hs B X D X' J' u; have he: τord H hs B X' D J' y=x:= (signΦ H hs X B X' D J' u).trans hU; let p:= p'.terra; let A:=incVec 1 (Point a); let S:= Maxwell.Free.score a A p p; refine ⟨S.re,fun hx=>?_ ,?_ ⟩
        · have hh:0 < Maxwell.Free.score a A p p:= Maxwell.Free.detects a A (position a) p (fun he=> hx (show x∈ Ghost G d' e from fun t=>Complex.ofReal_eq_zero.mp ((hq _).symm.trans (by rw [show p'.terra=0 from he,map_zero])))) -- cast failure likely
          exact Complex.lt_def.mp hh|>.1
        have hS: Maxwell.Free.bond G (incVec 1 (skew a)) (incVec 1 (Point a)) (turnT a p').terra p'.terra=S:=by rw [mirrored_saga,pole_align]; exact (summed ..).symm
        exact bosslim H hs X B X' D J' a hp Ht ht h' x y he S ((congr_arg (fun s=>Tendsto (fun i=> ((K0 H hs X X' D a (Ht i) (wrap _ (skew a)) (wrap _ (Point a)) hp (e:=e) 0 y y):ℂ)) atTop (𝓝 s)) hS).mp (nut H hs X B X' D J' a hp L Ht ht h' u p' Hp))
lemma Hear (s:Submodule ℝ (Bead G d' e))(hv:Disjoint s (Ghost G d' e)):
      ∀ᶠ i in atTop,∀ (x:Bead G d' e),x∈ s→x≠0→0 < boss H hs X B X' D J' (Ht i) a hp (wrap (t i) (skew a)) (wrap (t i) (Point a)) x x:=by
          choose g hz hh using fun x:s=> barPos H hs X B X' D J' a hp L Ht ht h' x.val
          have hg(x:s)(hp:x≠0):0<g x:= hz x (fun h=> hp (Subtype.ext (Submodule.disjoint_def.mp hv _ x.property h)))
          let F(i:ℕ):= pullD s.subtypeL (boss H hs X B X' D J' (Ht i) a hp (wrap (t i) (skew a)) (wrap (t i) (Point a)))
          filter_upwards [temple F g (fun x=> hh x) hg] with i hi; exact fun x h ht=> hi (⟨x,h⟩:s) (fun h=> ht (congr_arg Subtype.val h))
end YM.OPE.Quit.Jac
