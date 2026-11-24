import YM.FVA2.Facade.Scanner
/-!
 # Travel: full step open using RG10. Ticket already rescaled, Origin all

 `Commission` used only here as witness of positive Hessian on each looked-up
 internal slice. Provided by actual structure on the Fabric; won't need to suppose when
 applying to the genuine finite-regulator Wilson hierarchy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {G: Gauge} {c f n:Side}

variable {n:Side}{L:Fabric G n}
 def drive {n:Side}{L:Fabric G n}(T:Cloth L) (z:L.Cost→PowerSeries ℝ)(U:Unmasked G n) (A:Ticket (Flats G n)) (J:ChartRatio G)(h:Commission J T U z): Unmasked G (Bottom L) × Ticket (Flats G (Bottom L)):= match T with
 | .floor _ _ _=> (U,A)
 | .inLayer (t:=t) (L:=M) P C=> show Unmasked _ (Bottom M) × Ticket (Flats _ (Bottom M)) from drive (L:=M) C (z ∘ some) (Update P t J (z none) U (Exists.choose h)) (Broadcast P t J (z none) U (Exists.choose h) (boost (blankRight P) A)) J (Exists.choose_spec h)

private lemma lock_price {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](h:∀ x:E,x=0)(Q:Quadratic E) : Q.RespectsPrice:= by
 refine ⟨⟨Q.P,Q.side,?_,?_⟩,rfl⟩
 · exact ⟨1,one_pos,fun x=> by rw [h x]; simp⟩
 simp_rw [show ∀ x:E,Q.P x x=Q.P 0 0 from fun x=> by rw [h x]]; exact continuous_const
private lemma lock_mean {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] {F:Type} [NormedAddCommGroup F][NormedSpace ℝ F] (h:∀u:E,u=0) (a:Quadratic (E×F))(μ:Measure E)[μ.IsAddHaarMeasure](ha:(core a).RespectsPrice)(p:Ticket (E×F))(x:E)(y:F) : Stack.read y (uptake a μ ha p) = Stack.read (x,y) p:= by
 apply PowerSeries.ext; intro i;
 rw [uptime]; let v:= coeff i (Stack.read (x,y) p); let b:=one_ne_zero (α:=ℝ); let P:= ha.inner; simp_rw [show ∀ w:E,coeff i (Stack.read (w+skew a ha y,y) p)= v from fun w=> by unfold v; rw [h (_+_),h x] ];
 change P.average μ (fun _=>v)=v
 unfold Law.average; change (∫ x:E,v*P.kern x ∂μ)/_=v; rw [integral_const_mul]; field_simp [ne_of_gt (positive P μ)]

lemma holding {n:Side}{L:Fabric G n}(T:Cloth L)(z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(J:ChartRatio G)(h:Commission J T U z): (core (policy T z U)).RespectsPrice:= by
 cases T with
 | floor k b y=> exact lock_price (E:=Panel (Cloth.floor n b y)) (fun x=>funext fun i=>Empty.elim i) _
 | @inLayer c f S H t hf L P C=>
    exact Charged.ticket (bidding (P:=P) z U (Exists.choose h) J) (Exists.choose h) (holding C _ _ J (Exists.choose_spec h))
termination_by structural T

section Local
variable {he: Even n.val} {T:(endcap (G:=G) n he).loom.Truss} (U:Unmasked G n) (J:ChartRatio G)(z:(endcap (G:=G) n he).Cost→PowerSeries ℝ)
local notation "T0"=> Cloth.floor n he T
local notation "V"=> policy T0 z U
local notation "F"=> Panel T0
local notation "μ"=> tangent G (Warm T0)
local notation "K"=> ledge T0 z J U
lemma floors : packed T0 z= 1:= by unfold packed; change (∏ i:Empty,_)=_; simp
lemma moved_0 (_hj:LocalRatio J) : pending T0 z J=1:= by
 have ht: jacobian J (U:=Warm T0) = 1:= funext fun i=> by unfold Chart.jacobian; change (∏ i:Empty,_)=1; simp
 unfold pending; rw [floors z]; unfold tissue; rw [ht, Stack.rise_one]; simp [roll]
include J
lemma lock_den (hj:LocalRatio J)(h:(core (V)).RespectsPrice)(A:Ticket (Flats G n)) : uptake (V) μ h (K * boost (line T0) A)= U.W*A:= by
 let p:Ticket (Flats G n):= U.W*A; have hx A: boost (line T0) (U.W*A)= K* boost (line T0) A:= by unfold ledge; rw [moved_0 J z hj,mul_one,map_mul]
 erw [←hx A]; apply Stack.into; intro x; erw [lock_mean (E:=Panel (Cloth.floor n he T)) (fun a=>funext fun i=> Empty.elim i) (V) μ h _ (0:Panel (Cloth.floor n he T)) x,caught]
omit J
-- last tree doesn't freeze bottom variables here.
lemma lock_q (h:(core (V)).RespectsPrice) (x:Flats G n) : (reduced _ h).flourish x= U.Q.flourish x:= by
 change U.Q.flourish x+ (unpaid T0 z).flourish _= _; unfold unpaid; rw [bought];
 rw [add_eq_left]; change (∑ i:Empty, _)=_; simp
end Local
variable {J:ChartRatio G}
variable {L:Fabric G n}(T:Cloth L)(z:L.Cost→PowerSeries ℝ)
variable (U:Unmasked G n)(h:Commission J T U z)(hj:LocalRatio J)(u:incline U.W)(A:Ticket (Flats G n))

local notation "F"=> Panel T
local notation "V"=> policy T z U
local notation "Y"=> drive T z U A J h
local notation "μ"=> tangent G (Warm T)
local notation "p"=> ledge T z J U
local notation "q"=> holding T z U J h

-- Crest exposes the complete open-mass step iterations, retaining denominator.
-- fixed G n but any height
theorem achieves {n:Side}{L:Fabric G n}(T:Cloth L) (z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(h:Commission J T U z)(hj:LocalRatio J)(u:incline U.W)(A:Ticket (Flats G n)) : uptake (policy T z U) (tangent G (Warm T)) (holding T z U J h) (ledge T z J U * boost (line T) A)= (drive T z U A J h).1.W * (drive T z U A J h).2:= by
 cases T with
 | floor k b y=> rw [drive]; exact lock_den U J z hj _ A
 | @inLayer c f S H t hf L P C=>
    let U':= Update P t J (z none) U (Exists.choose h)
    let A':= Broadcast P t J (z none) U (Exists.choose h) (boost (blankRight P) A)
    let h':= Exists.choose_spec h
    unfold drive
    exact (sails z U (Exists.choose h) J A (holding C (z∘some) U' J h') hj u).trans (achieves C (z∘some) U' h' hj (funded hj (z none) u _) A')
termination_by structural T

theorem avowed {n:Side}{L:Fabric G n}(T:Cloth L) (z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(h:Commission J T U z)(hj:LocalRatio J)(A:Ticket (Flats G n)) : uptake (policy T z U) (tangent G (Warm T)) (holding T z U J h) (ledge T z J U)=(drive T z U A J h).1.W:= by
 cases T with
 | floor k b y=>
    rw [drive]; have h₀:= lock_den U J z (T:=y) hj 1 (h:=holding (Cloth.floor n b y) z U J h); erw [map_one,mul_one,mul_one] at h₀; exact h₀
 | @inLayer c f S H t hf L P C=>
    let u:= Exists.choose h
    let U':= Update P t J (z none) U u
    let A':= Broadcast P t J (z none) U u (boost (blankRight P) A)
    let h':= Exists.choose_spec h
    rw [drive]; exact (ticketed z U u J (holding C (z∘some) U' J h') hj).trans (avowed C (z∘some) U' h' hj A')
termination_by structural T

theorem receives {n:Side}{L:Fabric G n}(T:Cloth L) (z:L.Cost→PowerSeries ℝ)(U:Unmasked G n)(h:Commission J T U z)(A:Ticket (Flats G n)) (x): (drive T z U A J h).1.Q.flourish x=(reduced (policy T z U) (holding T z U J h)).flourish x:= by
 cases T with
 | floor k b y=> rw [drive]; exact (lock_q U z (T:=y) _ _).symm
 | @inLayer c f S H t hf L P C=>
    let u:= Exists.choose h
    let U':= Update P t J (z none) U u
    let A':= Broadcast P t J (z none) U u (boost (blankRight P) A)
    let h':= Exists.choose_spec h
    rw [drive]; exact (receives C (z∘some) U' h' A' x).trans (Charged.reduced_eq (bidding z U u J) (holding C (z∘some) U' J h') _ x).symm
termination_by structural T
include hj u
theorem forecasts : fit V μ q (boost (line T) A) p= (Y).2:= by
 have he:incline (ledge T z J U):= reserve T z U J hj u
 apply (worth (Quadratic.upright V μ q he)).mul_left_cancel
 rw [fit_eq _ _ _ _ _ he,achieves T z U h hj u A,avowed T z U h hj A]
end YM.FVA2.Facade
