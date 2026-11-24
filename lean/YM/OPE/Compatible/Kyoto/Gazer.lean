import YM.OPE.Compatible.Kyoto.Zag
import YM.OPE.Compatible.Kyoto.Fiscal
import YM.OPE.Compatible.Kyoto.Room
/-!
# Complex coefficient observations in frame coordinates

`ClockVal` assembles the real and imaginary observations on a basis
into a complex-linear map. `TintPic` identifies its value on a general
coefficient vector. Under the soundness, rate, and basis approximation
hypotheses of `eraW`, these maps eventually admit right inverses.
Both the maps and the chosen right inverses have upper rate zero.
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
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial
section
open Spells Lass Lass.Zest Ibis Labels Source
variable {L:PriceBook H T}{a:Axis}
variable (V:Foyer L hs a l (d+6))
set_option quotPrecheck false
local notation "vP"=> V.pay
local notation "Z!"=> V.pay.st
local notation "E!"=> Eagle (Z!).Glp (Z!).Z a (vP).policy
local notation "ν"=> V.pay.st
variable {he:highStage L hs a V  ≤ i} {hp:highStage L hs a V ≤ j}
variable (X:BankW L hs a V he p)
variable (Y:BankW L hs a V hp p')
variable {A: Labels.Frame G l}{U₀:Hol G}{S:SectionData A}
local notation "J!"=>A.Index
variable {P:A.Coeff→ Coefficient A n}{Q:Rep G n}
variable (P₁:Torch S U₀ 0 Q P d b)
variable (N:Cab T i p)
noncomputable abbrev hazard (V:Foyer L hs a l (d+6))(he:highStage L hs a V ≤ i):4  ≤ i:=V.pay.st.S.order_cut.trans he
variable (R':Spells.Pad G)
noncomputable def tintX (s:ℝ)(A':ℂ→L[ℝ]ℝ)(v:A.Coeff):solar G (d+6) V.pay.st.τ:= Torch.spark v P₁ s N.ℳ.gear (hazard V he) (Z!).hτ R' A' (K:=K)
noncomputable abbrev FaithV (s:ℝ)(x:A.Coeff)(M:ℂ→L[ℝ]ℝ):= τPledge X.cart N s (tintX V (he:=he) P₁ N R' s M x)
noncomputable def Swing (s:ℝ)(x:A.Coeff):= (FaithV V X P₁ N R' s x Complex.reCLM,FaithV V X P₁ N R' s x Complex.imCLM)
noncomputable def ClockVal (V:Foyer L hs a l (d+6)){he:highStage L hs a V ≤ i}(X:BankW L hs a V he p)(N:Cab T i p) (S:SectionData A)(R':Spells.Pad G){pU:Rep G n}{P:A.Coeff→ Coefficient A n} (P₁:Torch S U₀ 0 pU P d b)(s:ℝ) : A.Coeff→L[ℂ] BoxQ (dims V):=Pique (dims V) (fun i=>Swing V X P₁ N R' s (CastX (X:=A) i)) 
set_option maxHeartbeats 200000
lemma TilAP (s:ℝ)(x:A.Coeff) (hp:highStage L hs a V ≤ i): Torch.stars (K:=K) x P₁ s N.ℳ.gear (hazard V hp) (Z!).hτ R' = Arco (fun i=> (tintX V P₁ N R' s Complex.reCLM (CastX (X:=A) i) (he:=hp),tintX V P₁ N R' s Complex.imCLM (CastX (X:=A) i) (he:=hp))) x:= Torch.starsP x P₁ s N.ℳ.gear (hazard V hp) (Z!).hτ R'

lemma CoinL (s:ℝ)(x:A.Coeff): Swing V X P₁ N R' s x= Arco (fun i=>Swing V X P₁ N R' s (CastX (X:=A) i)) x:=by
        let F:= τPledge X.cart N s; let v(x):= Torch.stars x P₁ s N.ℳ.gear (hazard V he) (Z!).hτ R' (K:=K); let U:= A.Index; let W:U→_:= fun i=> v (CastX (X:=A) i)
        have hx(y:A.Coeff):Swing V X P₁ N R' s y=doublet F (v y):=rfl
        simp_rw[hx]; exact (congr_arg (fun q=> doublet F q) (show v x=Arco W x from TilAP V P₁ N R' s x he)).trans (strums F W x)
lemma LaidS (s:ℝ)(x:A.Coeff): (ClockVal V X N S R' P₁ s) x=Garm (dims V) (Swing V X P₁ N R' s x):=by
         unfold ClockVal; rw [Flare]; exact congr_arg (Garm (dims V)) (CoinL V X P₁ N R' s x).symm

variable (f:I→Cab T i p) {K₁:I→Side}{Q:∀ i,Rep G (K₁ i)}{P:∀ i,A.Coeff → Coefficient A (K₁ i)}
variable {b η s β:I→ℝ} (P₁:∀ i,Torch S U₀ 0 (Q i) (P i) d (b i)) (s:I→ℝ)
noncomputable abbrev AWake (i:I)(j:A.Index): Asp S U₀ d:= Torch.AspS (CastX (X:=A) j) (P₁ i) (s i)
local notation "AK"=> AWake P₁ s
local notation "TP" => fun i=> ClockVal V X (f i) S R' (P₁ i) (s i)
local notation "Rπ"=>FunLike 
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
private abbrev markedBasis (i : I) (j : A.Index) :=
  Cloz (D₀ := (Z!).stars) (V := Cab.ℳ) (AWake P₁ s) R' f (hp := hazard V he) i j

private lemma submittedCoordinate (i : I) (j : A.Index) (axis : ℂ →L[ℝ] ℝ) :
    tintX V (he := he) (P₁ i) (f i) R' (s i) axis (CastX (X := A) j) =
      DentP (D₀ := (Z!).stars) (V := Cab.ℳ) (AWake P₁ s) R' f (hp := hazard V he) i j axis := by
  rfl

private lemma submittedPair (i : I) (j : A.Index) :
    Swing V X (P₁ i) (f i) R' (s i) (CastX (X := A) j) =
      doublet (τPledge X.cart (f i) (s i)) (markedBasis V (he := he) R' f P₁ s i j) := by
  apply Prod.ext
  · exact congrArg (τPledge X.cart (f i) (s i))
      (submittedCoordinate V (he := he) R' f P₁ s i j Complex.reCLM)
  · exact congrArg (τPledge X.cart (f i) (s i))
      (submittedCoordinate V (he := he) R' f P₁ s i j Complex.imCLM)

private lemma clockAssembled (i : I) (x : A.Coeff) :
    SpinOrbit X.cart (AWake P₁ s) R' f (s i) i x =
      doublet (τPledge X.cart (f i) (s i)) (Arco (markedBasis V (he := he) R' f P₁ s i) x) := rfl

private lemma assembleMeasured {E F J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype J] (observer : E →L[ℝ] F)
    (source : J → E × E) (measured : J → F × F)
    (matchAt : ∀ j, measured j = doublet observer (source j)) (x : J → ℂ) :
    Arco measured x = doublet observer (Arco source x) :=
  (congrArg (fun h : J → F × F => Arco h x) (funext matchAt)).trans (strums observer source x).symm

private lemma clockOrbit (i : I) (x : A.Coeff) :
    Arco (fun j => Swing V X (P₁ i) (f i) R' (s i) (CastX (X := A) j)) x =
      SpinOrbit X.cart (AWake P₁ s) R' f (s i) i x := by
  exact (assembleMeasured (τPledge X.cart (f i) (s i)) (markedBasis V (he := he) R' f P₁ s i)
    (fun j => Swing V X (P₁ i) (f i) R' (s i) (CastX (X := A) j))
    (submittedPair V X R' f P₁ s i) x).trans (clockAssembled V X R' f P₁ s i x).symm

lemma TintPic (i:I)(x:A.Coeff) : (ClockVal V X (f i) S R' (P₁ i) (s i)) x=Garm (dims V) (SpinOrbit X.cart (AWake P₁ s) R' f (s i) i x):=by
  exact (Flare (dims V) (fun j => Swing V X (P₁ i) (f i) R' (s i) (CastX (X := A) j)) x).trans
    (congrArg (Garm (dims V)) (clockOrbit V X R' f P₁ s i x))
section
variable {l₀:Filter I}
open Pill
variable (hx:Torch.BondS P₁ β l₀ s) (hz: Wax β l₀ η (-1)) (ht:Tendsto β l₀ atTop)
variable (hΛ: Wax β l₀ (fun i=>(f i).fees) 0)(hS:S.Sound U₀)(hp':l<d+6)
variable (hK:∀ᶠ i in l₀,let N:=V.pay.st.τ 0; let u:=(K₁ i); let T:=(f i).ℳ.gear; let Y:=Hoard G (4*(P₁ i).B) (d+6) N; ∀ x∈Y,‖boostS (rentV G T (hazard V he) K.K u) (1/2) N (d+6) x - boostS (atlasF G T (hazard V he) K.K) (1/2) N (d+6) x‖ ≤ η i*‖x‖)
include hx hz ht hΛ hS hp' hK
lemma eraW : Wax β l₀ (fun i=> ClockVal V X (f i) S R' (P₁ i) (s i)) 0 ∧∃ Q:I→ BoxQ (dims V)→L[ℂ] A.Coeff, Wax β l₀ Q 0 ∧∀ᶠ i in l₀,(ClockVal V X (f i) S R' (P₁ i) (s i)).comp (Q i)=ContinuousLinearMap.id ..:=by
        let z:=(fun i=> (f i).ℳ.gear); let O:=(AWake P₁ s); let F:=TP
        have hL:Lineage (f:=l₀) η K.K z (hazard V he) s (fun i=>(Q i).p) O (V.pay.st.τ 0) (β:=β):= ⟨ht,fun i=> hx.Ties _ (Score.steady (CastX (X:=A) i) (carth ht)),hz,fun _=>hK,fun i=>Eventually.of_forall (fun x=>(P₁ x).kM.mark _),fun _ _=>rfl,fun _ _=>rfl⟩; have hRe:= fun i (x:A.Coeff)=> TintPic V X R' f P₁ s i x
        obtain ⟨hW,A,hY,hA⟩:= LaunchRank X.cart O R' f hL hΛ (show (-1:ℝ)/2<0 from by norm_num) (worthP hx.Lamp|>.pays (carth ht)) hS hp'; let S':=(Garm (dims V)).toContinuousLinearEquiv; let W(i:I):= A i ∘L S'.symm.toContinuousLinearMap
        have hv:Wax β l₀ W 0:=(Paintζ A (RateLE.const _ (carth ht)) _ hY).mono (by simp); let Z(i:I):=(fun i=> S'.toContinuousLinearMap ∘L SpinOrbit X.cart O R' f (s i) i) i;
        have H':Wax β l₀ Z 0:=(Paintζ _ hW _ (RateLE.const S'.toContinuousLinearMap (carth ht))).mono (by simp)
        refine ⟨ H'.transfer (Eventually.of_forall fun i=> Doom (F i) (Z i) (hRe i)), fun i=> Cloom (W i),hv.transfer (Eventually.of_forall fun _=> Dprice _),?_ ⟩; filter_upwards [hA] with i hi; apply Dcout; intro x; exact (hRe i _).trans ((congr_arg S' (DFunLike.congr_fun hi (S'.symm x))).trans (S'.apply_symm_apply _))
end
end
end YM.OPE.Stroke
