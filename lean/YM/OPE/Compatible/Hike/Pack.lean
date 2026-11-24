import YM.OPE.Compatible.Hike.Cross
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
local notation "F!"=>Fruition X' (lapPrice (Patch.L P) e)
variable (O U:solar G d τ→L[ℝ] solar G d τ)
variable (V:Even n.val)(x y:Site n)(R':Guard H hs X B D.aware O)(S':Guard H hs X B D.aware U)
variable (Aq:Attest G P d k e d' m τ n)(hp:Crest G P K.K m)(hz:Pins K P x y)
local notation "Π"=> (lampPO H hs B X D X' J')
local notation "Λ"=> Lingo r' (Quoin hs D B H X)
local notation "qρ"=> Quoin hs D B H X
abbrev annual (p q:Tracts G d τ)(i:ℕ):Token:=
     let P' : Tracts G d τ→ solar G d τ:=Fallix G D.aware K (X.U 0).gear P.order_cut
     PriceZ.Warp (X.U 0) (evenBoot K P V i) P.order_cut hs (spikeS K P x i) (spikeS K P y i) (O (P' p)) (U (P' q)) R
lemma annual_z (j:Phase)(p q:Lingo r' (Quoin hs D B H X))(i:ℕ): (annual hs X D O U V x y p.val q.val i).seq j.val=ensuing H hs X B D O U V x y j p q i:= by
     exact (pitch H hs X D.aware O U 0 i x y p.val q.val V j).symm
include R'
lemma annual_turn (p q:Tracts G d τ)(i:ℕ): annual hs X D O U V x y (Gift G D.aware p) q i= Ū*annual hs X D O U V x y p q i:=by
    let P':=Fallix G D.aware K (X.U 0).gear P.order_cut
    unfold annual; dsimp only; rw [show O (P' _)=_ from (show O (P' (Gift G D.aware p))= _ from (congr_arg O (Flick D.aware (X.U 0).gear P.order_cut p (K:=K))).trans (R'.pulse (P' p)))]; exact reckoning H hs .. -- h etc
omit R'
include S'
lemma annual_turn' (p q:Tracts G d τ)(i:ℕ): annual hs X D O U V x y p (Gift G D.aware q) i= Ū*annual hs X D O U V x y p q i:=by let P':=Fallix G D.aware K (X.U 0).gear P.order_cut; unfold annual; dsimp only; rw [show U (P' _)=_ from (show U (P' (Gift G D.aware q))= _ from (congr_arg U (Flick D.aware (X.U 0).gear P.order_cut q (K:=K))).trans (S'.pulse (P' q)))]; exact reckR H hs ..
include R' S' Aq hp hz J'
abbrev Wane := Fellow (Gift G D.aware) X' (lapPrice P.L e) (Freedom H hs X B X' D J')
abbrev annualP (p q:Fruition X' (lapPrice P.L e))(k:ℕ):Token:=⟨Flit H hs X X' D O U V x y hp 0 p q k,Flit H hs X X' D O U V x y hp 1 p q k, Flit H hs X X' D O U V x y hp 2 p q k⟩
lemma skated (pY q:Fruition X' (lapPrice P.L e))(j:ℕ):annualP H hs X X' D O U V x y hp (Wane H hs X B X' D J' pY) q j= Ū*annualP H hs X X' D O U V x y hp pY q j∧ annualP H hs X X' D O U V x y hp pY (Wane H hs X B X' D J' q) j= Ū*annualP H hs X X' D O U V x y hp pY q j:=by
     let f:= annual hs X D O U V x y; let g(x y:Lingo r' qρ) j:= f x.val y.val j; let t:= lampPO H hs B X D X' J'; let P':= ensuing H hs X B D O U V x y (r':=r'); let Q:= Flit H hs X X' D O U V x y hp (e:=e); have hx:∀ i x y,Sky (μ*μ) 6 (Q i x y):= sunV H hs X X' D O U V x y hp; have hw:∀ a x y, Thick (μ*μ) (P' a x y-Q a (t x) (t y)):= vogue H hs X B X' D J' O U V x y R' S' Aq hp hz; let L:=pickS H hs X B D r'; let U':= Wane H hs X B X' D J'; have hv(i j x' y'):(g x' y' j).seq (i:Phase).val=P' i x' y' j:=annual_z ..; have h: Surjective t:= Eave.coal_sur (G:=Bead G d') J' X; have he:∀ x,t (L x)=U' (t x):= pokeU H hs X B X' D J'
     constructor
     · refine fleece_shift t h L id U' id he (fun i=>rfl) P' Q g hv (fun i x' y' j=>?_) hx hw pY q j
       exact congr_arg (fun p:Token=>p.seq i.val) ( (show g (L x') (id y') j= _ from annual_turn H hs X B D O U V x y R' x'.val y'.val j).symm)|>.trans (hv i j (L x') (id y'))
     refine fleece_shift t h id L id U' (fun i=>rfl) he P' Q g hv (fun i x' y' j=>?_) hx hw pY q j
     exact congr_arg (fun p:Token=>p.seq i.val) ((show g (id x') (L y') j=_ from annual_turn' H hs X B D O U V x y S' x'.val y'.val j).symm)|>.trans (hv i j (id x') (L y'))
end YM.OPE.Quit.Jac
