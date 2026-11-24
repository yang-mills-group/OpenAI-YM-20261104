import YM.Integration.WilsonMacroscopicRichTestGeometry

/-! The signed macroscopic detector for one independently dated physical exterior.
The entire test is applied on its original two-position support. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSignedAmplitude
open Function Filter Set MeasureTheory YM.RG17 YM.OPE YM.OPE.Orbits YM.Spec YM.Extraction YM.Table
open YM.PhysMS YM.Trace.Pilot YM.Spin YM.Climb YM.Next.UVStress WilsonMacroscopicRichReflectedRoster
open WilsonMacroscopicRichMovingPlane WilsonMacroscopicRichTestGeometry
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{n:ℕ}

def stencil (J:ℝ→tower S)(φ:Test 2){τ:ℝ}(tp:0<τ)(w:(Bel C.book).Tag):External C S :=
  ⟨1,fun _=>physical J τ w,Next.UVStress.dilate tp φ⟩
def incoming (J:ℝ→tower S)(r:ℝ)(v:Fin n→(Bel C.book).Tag):Labels S (fun i=>(v i).1):=fun i=>J r _ (v i).2

def reading (J:ℝ→tower S)(φ:Test 2){τ:ℝ}(tp:0<τ)(w:(Bel C.book).Tag)(r:ℝ)(x:Points n)(v:Fin n→(Bel C.book).Tag):ℂ:=
  let X:=stencil J φ tp w
  X.test.applyTo fun z=>whole S (posed r x) (incoming J r v) (X.offset z) X.labels

def integrand (J:ℝ→tower S)(φ:Test 2){τ:ℝ}(tp:0<τ)(w:(Bel C.book).Tag)(r:ℝ)(x:Points n)(v:Fin n→(Bel C.book).Tag)(z:Points 2):ℂ:=
  let X:=stencil J φ tp w
  whole S (posed r x) (incoming J r v) (X.offset (τ•z)) X.labels

private theorem field (F:Spec.Final C f S)(J:ℝ→tower S)(φ:Test 2){τ:ℝ}(tp:0<τ)(w:(Bel C.book).Tag)(r:ℝ)(x:Points n)(v:Fin n→(Bel C.book).Tag)
    {z:Points 2}(safe:placed r τ x (relative z)∈conf (n+1)):
    integrand J φ tp w r x v z=S.useAt S (placed r τ x (relative z)) (Fin.append (fun i=>physical J r (v i)) (fun _:Fin 1=>physical J τ w)):=by
  let X:=stencil J φ tp w
  have same:X.offset (openRoot ((0:E4),τ•relative z))=X.offset (τ•z):=by
    change (fun i:Fin 1=>(openRoot (k:=1) ((0:E4),τ•relative z)) i.succ - (openRoot (k:=1) ((0:E4),τ•relative z)) 0) = fun i=>τ•z i.succ-τ•z 0
    funext i
    have zi:i=0:=Subsingleton.elim _ _
    subst i
    change τ•(z 1-z 0) - (0:E4)=τ•z 1-τ•z 0
    rw [sub_zero,smul_sub]
  have packed:absCord n 1 r (x,openRoot ((0:E4),τ•relative z))∈conf (n+1):=rebased x z ▸ safe
  have exactRead:=RG17.whole_absolutely (F:=F) X (incoming J r v) packed
  calc
    _=whole S (posed r x) (incoming J r v) (X.offset (openRoot ((0:E4),τ•relative z))) X.labels:=congrArg (fun e=>whole S (posed r x) (incoming J r v) e X.labels) same.symm
    _=S.useAt S (absCord n 1 r (x,openRoot ((0:E4),τ•relative z))) (Fin.append (fun i=>physical J r (v i)) (fun _:Fin 1=>physical J τ w)):=exactRead
    _= _:=congrArg (fun e=>S.useAt S e (Fin.append (fun i=>physical J r (v i)) (fun _:Fin 1=>physical J τ w))) (rebased x z)

private theorem positions (r τ:ℝ)(x:Points n):Continuous fun z:Points 2=>placed r τ x (relative z):=by
  apply (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
  intro i;cases i using Fin.addCases with
  | left i=>simpa [placed] using (continuous_const:Continuous fun _:Points 2=>r•x i)
  | right j=>
    have hz:Continuous (fun z:Points 2=>(relative z) j):=((continuous_apply j).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 1=>E4)).continuous).comp continuous_relative
    simp only [Fin.append_right];exact (show Continuous (fun _:Points 2=>τ) from continuous_const).smul hz

theorem purchased (F:Spec.Final C f S)(J:ℝ→tower S)(H:Leading F J)(φ:Test 2)(K:Set (Points n))(compact:IsCompact K)(safe:K⊆conf n)
    (v:Fin n→(Bel C.book).Tag)(w:(Bel C.book).Tag):
    ∃η:ℝ,0<η ∧ ∃B:ℝ,0≤B ∧ ∃U∈trail,∀r∈U,∀τ∈U,∀tp:0<τ,r/τ≤η → ∀x∈K,
      Integrable (fun z:Points 2=>φ z*integrand J φ tp w r x v z) ∧
      ‖reading J φ tp w r x v‖≤(∫z:Points 2,‖φ z‖)*B:=by
  obtain ⟨c,cp,space⟩:=clearance K compact safe φ
  obtain ⟨L,nz⟩:=WilsonMacroscopicRichTestGeometry.support φ
  obtain ⟨a,ap,B,Bp,U,hU,bill⟩:=WilsonMacroscopicRichDistantPoint.original F J H K _ compact L safe nz v w
  refine ⟨min a c,lt_min ap cp,B,Bp,U∩Ioi 0,inter_mem hU self_mem_nhdsWithin,?_⟩
  intro r hr τ hτ tp ratio x hx
  let zfield:=integrand J φ tp w r x v
  let t:=Fin.append (fun i=>physical J r (v i)) (fun _:Fin 1=>physical J τ w)
  have fit (u:Points 2)(hu:u∈tsupport φ):placed r τ x (relative u)∈conf (n+1):=space r τ hr.2 tp (ratio.trans (min_le_right _ _)) x hx u hu
  have flow:=positions r τ x
  have continuous_product:Continuous (fun u:Points 2=>φ u*zfield u):=by
    apply continuous_iff_continuousAt.mpr;intro u
    by_cases hu:u∈tsupport φ
    · apply φ.continuous.continuousAt.mul
      have good:=fit u hu
      have ev:∀ᶠz in 𝓝 u,placed r τ x (relative z)∈conf (n+1):=flow.continuousAt ((conf_open _).mem_nhds good)
      have h:ContinuousAt (fun z:Points 2=>S.useAt S (placed r τ x (relative z)) t) u:=
        (((S.class_smooth S F.room.kernel.smooth t).continuousOn.continuousAt ((conf_open _).mem_nhds good)).comp (f:=fun z=>placed r τ x (relative z)) flow.continuousAt)
      exact h.congr (ev.mono fun z hz=>(field F J φ tp w r x v hz).symm)
    · apply continuousAt_const.congr
      filter_upwards [(isClosed_tsupport (φ:Points 2→ℂ)).isOpen_compl.mem_nhds hu] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have proper:Integrable (fun u:Points 2=>φ u*zfield u):=continuous_product.integrable_of_hasCompactSupport (HasCompactSupport.mul_right φ.hasCompactSupport)
  refine ⟨proper,?_⟩
  have T:Integrable (fun z:Points 2=>φ z):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have budget (u:Points 2):‖φ u*zfield u‖≤‖φ u‖*B:=by
    by_cases hu:u∈tsupport φ
    · rw [norm_mul];apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [show zfield u= _ from field F J φ tp w r x v (fit u hu)]
      exact bill r hr.1 τ hτ.1 (ratio.trans (min_le_left _ _)) x hx _ ⟨u,hu,rfl⟩
    · simp [image_eq_zero_of_notMem_tsupport hu]
  change ‖(Next.UVStress.dilate tp φ).applyTo _‖≤_
  rw [Next.UVStress.zoom_integral]
  exact (norm_integral_le_of_norm_le (T.norm.mul_const B) (Eventually.of_forall budget)).trans_eq (integral_mul_const _ _)
end YM.Integration.WilsonMacroscopicRichSignedAmplitude
