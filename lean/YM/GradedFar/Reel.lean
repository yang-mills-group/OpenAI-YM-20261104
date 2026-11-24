import YM.GradedFar.Ripple
import YM.GradedFar.PhysicalBook
/-!
# Shape derivative charges of elected ordinary OPE in mixed radius frame

No Far argument here; to be used in differentiating expansion evaluated uniformly for fixed x ∈ compacta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting Orbits.Reader PhysMS
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open Tariff
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {n h:ℕ}{e:Fin n→ℕ} {d:ℕ} (o:E4) (r:ℝ)
local notation "θ"=> F.sector.derivatives
local notation "Ω"=> Reader.port R
local notation "K₁"=> arena F R d o r
-- coordinate OPE in comparison (assign basis): multilinear
variable (l:Toon G d)
def messenger (x:Points n) : MultilinearMap ℂ (fun i:Fin n=>Sec G (e i)) ℂ :=
    ((coord l).comp (assign J r d).symm.toLinearMap).compMultilinearMap
      ((Fork.packetCost F (sites o r x) o d R).compLinearMap (fun i=> (assign J r (e i)).toLinearMap))
lemma alarm (x:Points n)(u: AppointedH140Inputs G e): messenger F J R o r l x u=coord l (GradedFar.packet F J R d o r x u):= by
    unfold messenger GradedFar.packet; rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, LinearMap.comp_apply, Fork.packetCost_apply]; rfl
lemma resurface (H:AppointedH140Through h e) (hw:∀ i (u:Sec G (e i)),assign J r h (up (H i) u)= (θ).rise (H i) (assign J r (e i) u)) (x:Points n)(u:AppointedH140Inputs G e) :
    messenger F J R o r l x (GradedFar.raised H u)= messenger F J R o r l x u:= by
    rw [alarm,alarm]; change coord l ((assign J r d).symm (R.packet d _ _ o))= coord l ((assign J r d).symm (R.packet d _ _ o))
    apply congrArg; apply congrArg; unfold labels FVA2.GradedFar.raised; simp_rw [hw]; exact Fork.packet_inclusion ..
-- tag push at common cap: exactly unscale push (also when r =0)
private def cob (a:Axis)(v:Sec G h):Sec G (h+1):= (assign J r (h+1)).symm ((θ).deriv h a (assign J r h v))
private lemma arrival {d:ℕ} (u:S.Field d): (θ).rise le_rfl u=u:= (θ).arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection u
lemma reforest (x:Points n) (v:ListInput G n h) (i:Fin n) (a:Axis) (Hu:Going F J h r) (d:ℕ):
 R.packet d (sites o r x) (voices (Window.elevate F (fun j=> ⟨h, (labels J r v) j⟩) i a)) o =
     R.packet d (sites o r x) (labels J r (update (climbing v) i (cob F J r a (v i)) : ListInput G n (h+1))) o := by
 let v₂:Fin n→S.Tag:= fun j=> ⟨h,labels J r v j⟩; let q:=Window.elevate F v₂ i a
 let move (j:Fin n)(p:S.Tag) (H:p.1 ≤ h+1) := (θ).rise H p.2 -- avoid dependent motive chaos
 have hi:q i=⟨h+1,(θ).deriv h a (assign J r h (v i))⟩:=update_self ..
 have hj(j:Fin n)(he:j ≠ i) : q j = ⟨h,assign J r h (v j)⟩:=update_of_ne he ..
 have H: ∀ j,(q j).1 ≤ h+1:=by intro j; by_cases he:j=i; subst j; rw [hi]; rw [hj j he]; exact Nat.le_succ _
 let z:ListInput G n (h+1):= update (climbing v) i (cob F J r a (v i))
 have he : (fun j=> move j (q j) (H j))= labels J r z := by
    funext j; unfold labels z; by_cases hh:j=i
    · subst j; rw [update_self]; have hp (q:S.Tag)(h0:q=⟨h+1,(θ).deriv h a (assign J r h (v i))⟩) (he:q.1 ≤ h+1):
         move i q he = assign J r (h+1) (cob F J r a (v i)):= by
           subst q; rw [cob,LinearEquiv.apply_symm_apply]; exact arrival F _
      exact hp (q i) hi (H i)
    rw [update_of_ne hh]; have hp (q:S.Tag)(h0:q=⟨h,assign J r h (v j)⟩)(he:q.1 ≤ h+1) : move j q he=assign J r (h+1) (climbing v j):= by
       subst q; exact (Hu _).symm
    exact hp (q j) (hj j hh) (H j)
 change R.packet d _ (voices q) o= R.packet d _ (labels J r z) o; rw [← he]; exact (Fork.packet_inclusion F _ _ _ R H (voices q)).symm
lemma breeze (x:Points n)(hx:K₁ x)(u:AppointedH140Inputs G e): ContDiffAt ℝ ∞ (fun x=>messenger F J R o r l x u) x:= by
 simp_rw [alarm]; let L:= (((coord l).comp (assign J r d).symm.toLinearMap).restrictScalars ℝ).toContinuousLinearMap
 exact L.contDiff.contDiffAt.comp x (packet_shine F R d o r (fun i=>⟨e i,labels J r u i⟩) hx)
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
lemma along_deriv (Hu:Going F J h r)(u:ListInput G n h)(x:Points n)(i:Fin n×Axis)(b:ℝ)(hx:K₁ (slopePath x (Points.direction i.1 i.2) b)): HasDerivAt (fun s=> messenger F J R o r l (slopePath x (Points.direction i.1 i.2) s) u)
    (messenger F J R o r l (slopePath x (Points.direction i.1 i.2) b) (update (climbing u) i.1 (push F J h i.2 r (u i.1)) : ListInput G n (h+1))) b:=by
 rw [show push F J h i.2 r (u i.1)=(r:ℂ) • cob F J r i.2 (u i.1) from rfl,(messenger F J R o r l _).map_update_smul]; simp_rw [alarm]
 let L:= (((coord l).comp (assign J r d).symm.toLinearMap).restrictScalars ℝ).toContinuousLinearMap
 obtain he:= L.hasFDerivAt.comp_hasDerivAt b (packet_year F R d o r (fun j : Fin n=> ⟨h,labels J r u j⟩) x i b hx); rw [reforest F J R o r _ u i.1 i.2 Hu d, map_smul] at he; exact he
lemma mete (Hu:Going F J h r)(u:ListInput G n h)(x:Points n)(i:Fin n×Axis)(hx:K₁ x): Points.gradient i.1 i.2 (fun y=> messenger F J R o r l y u) x=
    messenger F J R o r l x (update (climbing u) i.1 (push F J h i.2 r (u i.1)) : ListInput G n (h+1)):= by
 have hu:slopePath x (Points.direction i.1 i.2) 0=x:= Crosser.endsZero x _
 obtain ht:= (slope_chain x (Points.direction i.1 i.2) 0 (show DifferentiableAt ℝ (fun y=> messenger F J R o r l y u) _ from by rw [hu]; exact (breeze F J R o r l x hx u).differentiableAt (by simp))).unique (along_deriv F J R o r l Hu u x i 0 (by rw [hu]; exact hx)); rw [hu] at ht; exact ht
end YM.Integration.GradedFar.Window
