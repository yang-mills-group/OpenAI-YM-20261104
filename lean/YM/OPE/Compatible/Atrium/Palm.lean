import YM.OPE.Compatible.Atrium.Yet
/-! # Virtual frame noise sensor Jet. Mean local across periods. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K: KernelChoices}
namespace Script
open Virgin
def reckon (P:Patch)(U:CoverConfig G)(j:Axis):= entryCap P U * victoryBox P U j * (entryCap P (hall P U j))⁻¹
def yodel (G:Gauge)(P:Patch)(K:KernelChoices)(j:Axis)(x:maskShelf G P):= K.penalty * G.price (G.lieExp (vibe G P j x) * (reckon P (hornU G P x) j)⁻¹)
lemma thinks (h:P.Branches K G)(j:Axis) : ContDiffAt ℝ ω (yodel G P K j) 0:=by
    let T:= hornU G P; have hv:T 0=1:=horn_unit ..; have he(j):ContDiffAt ℝ ω (fun x=>G.mat (victoryBox P (T x) j)) 0:=by
        refine (show ContDiffAt ℝ ω (fun i=> G.mat (G.focus i)) (litBox P (T 0) j) by rw [hv,lit_ground h]; exact G.focus_diff).comp (f:=fun x=> litBox P (T x) j) _ (gulf_height h (hornDiff G P) hv j)
    let R x:= reckon P (T x); have ht : Army R 0:=by
       intro i; simp only [R,reckon,G.mat_mul,G.mat_inv]; have hh : Army (fun x (_:Axis)=>entryCap P (hall P (T x) i)) 0:= fun _=>cap_fold h (hallUp (hornDiff G P) P i) (by rw [hv,hall_one]); exact ((cap_fold h (hornDiff G P) hv).mul (he i)).mul (hh.inv i)
    apply ContDiffAt.mul contDiffAt_const (Work.F03.price_smooth (A:=fun x=> G.lieExp (vibe G P j x) * (R x j)⁻¹) ?_); simp only [G.mat_mul]; exact (G.exp_jet.contDiffAt.comp (f:=vibe G P j) _ (vibe G P j).contDiff.contDiffAt).mul (ht.inv j)
variable (hp:Odd S.ratio.count.val)
abbrev gustU (t:S.Choices)(p:Site c)(a:Axis)(x:vertP S.ratio hp G):= S.kernel.penalty * G.price (represent x.1 (p,a)*(S.prediction (fieldF _ x.2) t (p,a))⁻¹)
set_option maxHeartbeats 200000 in
lemma turnsAt (h:S.patch.Branches S.kernel G)(t:S.Choices)(p:Site c)(j:Axis) : gustU hp t p j =ᶠ[𝓝 0] yodel G S.patch S.kernel j ∘ (nick hp p):=by
     let P:=S.patch; let V(x:vertP S.ratio hp G):= fieldF (forest S.ratio hp) x.2; let Y:= fun x=>expandAt (S.ratio.embed p) (V x); let U:= hornU G P ∘ nick hp p; have hx(x): V x=input G f (Stationary.pad (forest S.ratio hp) x.2) := spoolP _ _
     have hV: V 0=1:=by rw [hx]; change input G f (Stationary.pad (forest S.ratio hp) 0)=_; rw [map_zero,input_zero]
     have he: Army V 0:= by rw [funext hx]; exact Army.powL (v:=fun x:vertP S.ratio hp G=>Stationary.pad (forest S.ratio hp) x.2) ((Stationary.pad (forest S.ratio hp)).contDiff.contDiffAt.comp (f:=Prod.snd) (0:vertP S.ratio hp G) contDiffAt_snd)
     have ha: Y 0=1:=by unfold Y; rw [hV]; rfl
     let A:= nick hp p (G:=G); have hh: U 0=1:= by change hornU G P (A 0)=_; rw [map_zero, horn_unit]
     have hy: Army U 0:= ((show Army (hornU G P) (A 0) from A.map_zero.symm ▸ hornDiff G P)).comp A.contDiff.contDiffAt
     have hu:=plaza_agree h (U:=Y) (fun i=> he _) ha hy hh (Eventually.of_forall fun v i hi k=> chairU hp p v (i,k) hi)
     filter_upwards [hu,centered_wire S t h he hV p j,centered_wire S t h he hV (p+step j) j] with i hi hz hr
     have hq : S.prediction (V i) t (p,j)=reckon P (U i) j:= by
         have ha:=hz.2
         rw [hz.1,hr.1, ← house_moves] at ha
         have hf : victoryBox S.patch (Y i) j= victoryBox P (U i) j:= (hi.2 j).1; have hl:entryCap P (Y i)=entryCap P (U i):=by simp only [P,entryCap,entryHat,hi.1]
         have ht:entryCap P (hall P (Y i) j)=entryCap P (hall P (U i) j):=by simp only [P,entryCap,entryHat,(hi.2 j).2]
         change (entryCap P (Y i))⁻¹ * _ *entryCap P (hall P (Y i) j) = victoryBox P (Y i) j at ha
         unfold reckon; rw [hl,ht,hf] at ha; rw [← ha]; group
     change _ * G.price (_*_) = _ * G.price (G.lieExp (vibe _ _ j _)* (reckon P (U i) j)⁻¹); rw [←hq, chairV]
end Script
end YM.OPE.Flume
