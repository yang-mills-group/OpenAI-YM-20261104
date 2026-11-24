import YM.OPE.Compatible.Broma.Maj
/-! # enrolled thermal stage op
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
section
-- closure
variable {r s:M→ℝ}
lemma brimDown [NormedAddCommGroup E][NormedSpace ℝ E] {p q:M→ E→L[ℝ] E}(h:Brim p q r s) (hp:1≤r) (hs:0 ≤ s) (V:Submodule ℝ E) (x y:M→V→L[ℝ] V) (hx:∀ i a,↑(x i a)=p i a.val) (hy:∀ i a,↑(y i a)=q i a.val): Brim x y r s:=by
     have hk (s : M→ℝ) (u:M→E→L[ℝ] E) (x:M→V→L[ℝ] V) (h:Wealth u r s) (hx:∀ i a,↑(x i a)=u i a.val) (hs:0≤s): Wealth x r s:=by
          obtain ⟨c,hc,k,H⟩:= h; refine ⟨c,hc,k,fun i=>?_⟩; refine (x i).opNorm_le_bound (mul_nonneg (mul_nonneg hc (pow_nonneg (zero_le_one.trans (hp _)) _)) (hs _)) (fun a=>?_) ; rw [← Submodule.norm_coe,hx]; exact ((u i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (H i) (norm_nonneg _))
     exact ⟨hk _ _ _ h.A hx zero_le_one,hk _ _ _ h.B hy zero_le_one,hk _ _ _ h.D (fun i a=>show ((x i a).val-(y i a).val)= _ from by rw [hx,show (y i a).val=_ from hy ..]; rfl) hs⟩
lemma brimPlus [NormedAddCommGroup E]{X Y U V:M→E}(h:Brim X Y r s) (hp:Brim U V r s) (hr:1 ≤ r) (hs:0 ≤ s): Brim (X+U) (Y+V) r s:=by refine ⟨fortSum h.A hp.A hr zero_le_one, fortSum h.B hp.B hr zero_le_one,?_⟩; rw [add_sub_add_comm]; exact fortSum h.D hp.D hr hs
end
-- local indexing
variable (B:Medal P G K.K P.J) (H:LocalRatio R) (hp:Crest G P K.K m) (hs:G.Simple) (ha:Aware d τ)
local notation "X!" => TileC T P p R b
local notation "u!" => (upperX:X!→ℝ)
local notation "q!" => (downK:X!→ℝ)
-- therm
noncomputable def advancing (B:Medal P G K.K P.J) (H:LocalRatio R) (hs:G.Simple) (V:Sailing T P p R b) (hp:Aware d τ) (i:ℕ): Tower (Shade G) d τ →L[ℝ] Tower (Shade G) d τ:= rebase G hp (-(V.fare i)) ∘L YangZ B H hs V hp 0 i
noncomputable def season (B:Medal P G K.K P.J) (H:LocalRatio R) (hs:G.Simple) (V:Sailing T P p R b) (hp:Aware d τ) (i:ℕ): solar G d τ→L[ℝ] solar G d τ:=
    (advancing B H hs V hp i ∘L (solar G d τ).subtypeL).codRestrict _ (fun x=>aboard _ hp _ (actors 0 _ _ _ _ hp x.val x.property))
include H hs hp
lemma brimBeta :Brim (fun i:X! => rebase G ha (- betaA i)) (fun i:X! => rebase G ha (- betaE i)) u! q!:=by
     let x:= upperX (H:=T) (P:=P) (p:=p) (V:=R) (C:=b); have hx: (1:X!→ℝ)≤x:=max_cap _ _ _ _ _ --
     have he: (0:X!→ℝ) ≤ q! :=fun i=>by unfold downK; positivity
     have hZ(v:ℝ) : traceOf G (-v) ha= v • (traceOf G (-1) ha):=by
          apply ContinuousLinearMap.ext; intro i; let y:= peakV G ha (i 0); change Pi.single (M:=fun x:Phase=> Seat (d+x.val) (τ x) (Shade G)) 2 (((-v/2) • peakV G ha) (i 0))=v • Pi.single 2 ((((-1:ℝ)/2) • peakV G ha) (i 0)); have hw:(-v)/2=v*(((-1:ℝ)/2)):=by ring
          rw [hw,_root_.smul_apply,_root_.smul_apply,← smul_smul]; exact map_smul (LinearMap.single ℝ _ _) ..
     let S:= traceOf G (-1) ha; let p' (i:X!):=betaA i • S; let q(i:X!):=betaE i • S; have hv: Brim p' q x q!:=by
          obtain ⟨a,h₁,n,H'⟩:= (energyProd (H:=T) (p:=p) (C:=b) H hp hs).2.1
          refine Brim.oneOf ?_ ⟨a*‖S‖,mul_nonneg h₁ (norm_nonneg _),n,fun i=>?_⟩ hx (fun i=>pow_le_one₀ (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)) -- lacks E?
          · refine ⟨max b 0*‖S‖,mul_nonneg (le_max_right ..) (norm_nonneg _),0,fun i=>?_⟩; unfold p';rw [norm_smul]; simp only [pow_zero,mul_one, Pi.one_apply];exact mul_le_mul_of_nonneg_right ((i.1.1.bound i.2).trans (le_max_left ..)) (norm_nonneg _)
          rw [Pi.sub_apply]; unfold p' q; rw [←sub_smul (betaA i) (betaE i) S,norm_smul]; exact (mul_le_mul_of_nonneg_right (H' i) (norm_nonneg S)).trans_eq (by unfold x;ring)
     let f:=fun _:X! => (1:Tower (Shade G) d τ →L[ℝ] Tower (Shade G) d τ); rw [show (fun i:X! => rebase G ha (-betaA i))=f+p' from funext fun i=>congr_arg (1+·) (hZ _), show (fun i:X! => rebase G ha (- betaE i))=f+q from funext fun i=>congr_arg (1+·) (hZ _)]; exact brimPlus (Brim.constant _) hv hx he
lemma checked (he:∀ i,τ i ≤ m): Brim (fun i:X! => season B H hs i.1.1 ha i.2) (fun i:X! =>season B H hs i.1.2 ha i.2) u! q!:=by
      have hx: 1 ≤ u!:= max_cap (P:=P) (p:=p) (H:=T) (V:=R) (C:=b); have ht:(0:X!→ℝ)≤q!:=fun i=>by unfold downK; positivity
      have hP:= affordZ (p:=p) (b:=b) (T:=T) B H hs hp ha 0 he; apply brimDown (Canal hP (brimBeta H hp hs ha) hx ht) hx ht; · exact fun _ _=>rfl
      exact fun _ _=>rfl
end YM.OPE.Drift
