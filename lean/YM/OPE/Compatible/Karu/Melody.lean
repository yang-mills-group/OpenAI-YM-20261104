import YM.OPE.Compatible.Karu.Rit
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
variable (B: Medal P G K.K P.J)
variable (F:Sailing T P p R b)(H:Even c.val)
open Hark
variable (x y:Site c)(ψ:Phase)
local notation "S'"=>Sailing T P p R b
local notation "q!"=> χV P d
-- commute roll seam μ vector.Bi pulse.Ax
section pair
variable {W:Type}{T D E G:Type}[NormedAddCommGroup T][NormedAddCommGroup D][NormedSpace ℝ T][NormedSpace ℝ D]
local notation "X!"=>D→L[ℝ] D
local notation "MΦ"=>T→L[ℝ] D
lemma guestQ (p' q':W→Dice D)(Υ Ω:X!)(G:W→ X!)(u:W→ MΦ)(v:W→ MΦ)(t:W→ T→L[ℝ] T)(hz:∀ i,Υ.comp (G i)=(G i).comp Υ)(hH:∀ i,Ω.comp (G i)=(G i).comp Ω)(h:∀ i,(G i).comp (u i)= (v i).comp (t i))(μ:W→ Side){s:W→ℝ}(hs:0≤s)(hp:NPay μ (fun i=>p' i-pullD (G i) (q' i)) 0 s)(he:NPay μ u 0 1):
   NPay μ (fun i=> rollD (Υ.comp (u i)) (Ω.comp (u i)) (p' i)-pullD (t i) (rollD (Υ.comp (v i)) (Ω.comp (v i)) (q' i))) 0 s :=by
       let P(i):=Υ.comp (u i); let D(i):= Ω.comp (u i); let a(i):= p' i-pullD (G i) (q' i)
       have ht' : NPay μ P 0 1:=by simpa only [one_mul,Nat.add_zero] using! (FarCap (z:=P) (constantV (k:=0) μ Υ) he zero_le_one (fun i=>ContinuousLinearMap.opNorm_comp_le Υ (u i)))
       have hv : NPay μ D 0 1:=by simpa only [one_mul,Nat.add_zero] using! (FarCap (z:=D) (constantV (k:=0) μ Ω) he zero_le_one (fun i=>ContinuousLinearMap.opNorm_comp_le Ω (u i)))
       have he:NPay μ (fun i=>rollD (P i) (D i) (a i)) 0 s:=by simpa only [mul_one,Nat.add_zero] using! (flyP (K:=a) ht' hv hs zero_le_one hp)
       convert! he using 1; funext i; unfold a; rw [drag]; apply congrArg (fun y=> rollD (P i) (D i) (p' i)-y); apply ContinuousLinearMap.ext; intro x; apply ContinuousLinearMap.ext; intro y; change q' i (Υ ((v i) (t i x))) (Ω ((v i) (t i y)))= q' i ((G i) (Υ (u i x))) ((G i) (Ω (u i y)))
       rw [show v i (t i x)= _ from (DFunLike.congr_fun (h i) x).symm, show v i (t i y)= _ from (DFunLike.congr_fun (h i) y).symm]; exact congrArg₂ (fun x y=> q' i x y) (DFunLike.congr_fun (hz i) _) (DFunLike.congr_fun (hH i) _)
end pair
abbrev βX (P:Patch)(k:ℕ):ℝ:= (P.L.val:ℝ)⁻¹^k
lemma hostV (L P:Side)(i j:ℕ): ((CountL L P i).val:ℝ)⁻¹^j=(L.val:ℝ)⁻¹^j *((P.val:ℝ)⁻¹^j)^i:=by rw [hosts,mul_inv,mul_pow ,←inv_pow _ i]; rw [←pow_mul,mul_comm i j,pow_mul] -- name
variable (hY:∀ i, Y.comp (season B hp hs F hq i)=(season B hp hs F hq i).comp Y) (hZ:∀ i,Z.comp (season B hp hs F hq i)=(season B hp hs F hq i).comp Z)
local notation "VQ"=>Fitt Y Z hp hq hs F H x y ψ
local notation "LΦ"=>culm B hp hs F hq
lemma fluting (i:ℕ): (season B hp hs F hq i).comp (PeakA (F.U i) P.order_cut hq)= (PeakA (F.U (i+1)) P.order_cut hq).comp (culm B hp hs F hq i):=by
    apply ContinuousLinearMap.ext; intro x; unfold culm PeakA; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
lemma wageV {V:Type}[NormedAddCommGroup V] (p:ℕ→ℕ→ V) (h:NPay (fun i:ℕ × ℕ=> CountL c P.L i.2) (fun i=>p i.1 i.2) 0 (Scape.gDump (fun i=> CountL c P.L i.2) k)):
     ∃ b,∀ i j, ‖p i j‖ ≤ b*(βX P k)^j:=by
        obtain ⟨b,hb,H⟩:= bundleP.1 h; refine ⟨b*((c.val:ℝ)⁻¹)^k,fun i j=>?_⟩; have ht:= H (i,j); rw [pow_zero,mul_one] at ht; apply ht.trans_eq; change b*((CountL c P.L j).val:ℝ)⁻¹^_= _; rw [hostV]; unfold βX; ring
include hY hZ he
lemma gustP (ha:barrier P≤ c.val)(ht:Pins K P x y)(hQ:∀ i,τ i≤m)(hx:∀ i,Rise.stamp' d G k+44 ≤ τ i):∃ b,∀ i j,‖Hark.ErrS (VQ) (LΦ) i j‖≤ b*(βX P k)^j:=by
   let X(i:ℕ × ℕ): TileC T P p R b:=((F,F),i.1); let t:= keel X B hp; let n(i:ℕ × ℕ):=CountL c P.L i.2; have h(i): Even (n i).val:= evenBoot K P H i.2; have hv(i):barrier P≤(n i).val:=ha.trans (stalk c P.L i.2); have hh(i):upperX (X i) ≤ F.cost:= (max_self ..).le; obtain ⟨u',hu,Ht⟩:= ht
   have hb:=Temp X B hp F.cost hh he ((hx 0).trans (hQ 0)) hs; let q(i:ℕ× ℕ):=spikeS K P x i.2; let r(i:ℕ×ℕ):=spikeS K P y i.2; let A:=VarB X B hp F.cost hh he hQ hq hs
   let g(i:ℕ × ℕ):= season B hp hs F hq i.1; let v:0 ≤ (fun _:ℕ × ℕ=>F.cost):= fun i=>zero_le_one.trans F.fits
   let p(i:ℕ×ℕ):= ArmZ (F.U i.1) (spikeS K P x (i.2+1)) (spikeS K P y (i.2+1)) (evenBoot K P H _) hs P.order_cut hp (v i) ψ (d:=d) (τ:=τ); let e(i:ℕ × ℕ):=ArmZ (F.U (i.1+1)) (q i) (r i) (h i) hs P.order_cut hp (v i) ψ (d:=d) (τ:=τ)
   have hG: Cash n 0 (Scape.gDump n k) (fun i=> ‖p i-pullD (g i) (e i)‖):= t.beacon h hv P.order_cut P.order_cut hs v v hp hq hb A q r u' hu (fun i=> Ht i.2) hx ψ
   let f(i):= LA hq (X i); let b'(i):= LA hq (fallsF (X i)); let T(i:ℕ × ℕ):= (LΦ) i.1; have hW(i): (g i).comp (f i)=(b' i).comp (T i):= fluting hp hq hs B F i.1
   have hz:(NPay n (fun i:ℕ × ℕ=> Hark.ErrS (VQ) (LΦ) i.1 i.2) 0 (Scape.gDump n k)):= guestQ p e Y Z g f b' T (fun i=> hY _) (fun i=>hZ _) hW n (Scape.gDuty _ _) (show NPay n (fun i=> p i-pullD (g i) (e i)) 0 _ from hG) ((FitZ hq he X F.cost hh).1)
   exact wageV (Hark.ErrS (VQ) (LΦ)) hz
end YM.OPE.Quit.PriceZ
