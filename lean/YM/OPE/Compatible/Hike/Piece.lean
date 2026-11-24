import YM.OPE.Compatible.Karls.Bent
import YM.OPE.Compatible.Lob.Lip
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Karls.Bruno
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

lemma sky_uni {p q:ℕ→ℝ}(h:Sky b k p)(ht:Sky b k q)(hp:Thick b (p-q)):p=q:= sub_eq_zero.mp ((h.sub ht).blind hp)
-- static progression for mats susp read
lemma fleece_shift {A B:Type}(T:A→B)(h:Surjective T)(U₁ U₂:A→A)(V₁ V₂:B→ B)(hv:∀ i,T (U₁ i)= V₁ (T i))(hv':∀ i,T (U₂ i)= V₂ (T i))
   (X:Phase→ A→A→ℕ→ ℝ)(Y':Phase→B→B→ℕ→ℝ)(σ:A→A→ℕ→ Token)(hk:∀ i j x y,(σ x y j).seq (i:Phase).val=X i x y j)(hQ:∀ i x y j, (Ū*σ x y j).seq (i:Phase).val=X i (U₁ x) (U₂ y) j)
   (hz:∀ i x y,Sky v m (Y' i x y))(hp:∀ i x y,Thick v (X i x y-Y' i (T x) (T y))) :
    ∀ x y j,
     let P:= fun k r s=>(⟨Y' 0 r s k, Y' 1 r s k, Y' 2 r s k⟩:Token)
     P j (V₁ x) (V₂ y)=Ū* P j x y:=by
       intro x y j P; obtain ⟨x,rfl⟩:= h x; obtain ⟨y,rfl⟩:=h y; rw [←hv,←hv']; apply JetS.eta
       · let f:=Y' 0 (T (U₁ x)) (T (U₂ y)); have hx: X 0 (U₁ x) (U₂ y)=0:= funext fun j=> (hQ 0 x y j).symm.trans (boneS _); have hF:= hp 0 (U₁ x) (U₂ y); rw [hx,zero_sub] at hF; have hr: f=0:= (hz _ _ _).blind (by obtain ⟨⟨z,h₁,h₂,c,h₃⟩⟩:= hF; exact Thick.hex ⟨c,fun i=> (by rw [← norm_neg (f i)]; exact h₃ i)⟩ h₁ h₂ ); change f j= _; rw [hr]; exact (boneS _).symm
       · let f:=Y' 1 (T (U₁ x)) (T (U₂ y)); have hx:X 1 (U₁ x) (U₂ y)=X 0 x y:=funext fun j=> (hQ 1 x y j).symm.trans ((boneL ..).trans (hk 0 ..)); let g:=Y' 0 (T x) (T y); have h: g=f:=by
              apply sky_uni (hz 0 _ _) (hz 1 _ _); rw [show g-f=(X 1 (U₁ x) (U₂ y)-f)-(X 0 x y-g) from by rw [hx];abel]; exact (hp ..).sub (hp ..)
         exact (congr_fun h.symm j).trans (boneL (P j (T x) (T y))).symm
       let f:=Y' 2 (T (U₁ x)) (T (U₂ y)); have hx:X 2 (U₁ x) (U₂ y)=X 1 x y:=funext fun j=> (hQ 2 x y j).symm.trans ((boneH ..).trans (hk 1 ..)); let g:=Y' 1 (T x) (T y); have h: g=f:=by
          apply sky_uni (hz 1 _ _) (hz 2 _ _); rw [show g-f=(X 2 (U₁ x) (U₂ y)-f)-(X 1 x y-g) from by rw [hx];abel]; exact (hp ..).sub (hp ..)
       exact (congr_fun h.symm j).trans (boneH (P j (T x) (T y))).symm
end YM.OPE.Quit.Jac
