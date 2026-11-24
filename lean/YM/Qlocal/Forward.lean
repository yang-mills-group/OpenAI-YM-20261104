import YM.Qlocal.Clock
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Binding
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Work.F03 Work.F05
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped BigOperators Topology ENNReal Classical InnerProductSpace MatrixOrder ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {S:StepData c f} {k t j:ℕ}
    {V:Type} [DecidableEq V] {B:Census V}
open Primitives.TwoWave Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open AllOrder Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money
open Work.G05 Kinetic.Port
open PertExtension.Series Radial Floe Pace Haiku Filter
variable (R: PathData G) (u:Clip) (P: Floe.Layout G) (U:Finset Age) (p:Coin) {f0:ℝ→ℝ} (ha:Act t f0 p)(hb:p 0=0)
-- explicit forward affine bank in g⁻²-logPrice, with additional e/r. s positive on admission neighborhood; avoid claim away from there.
def charge (f0:ℝ→ℝ) (i:Age)(x:ℝ)(V:Config G n):= (1+f0 x)^ elapsed i * Floe.sketch P i n x V
def beforeLoop (f0:ℝ→ℝ)(x:ℝ)(V:Config G n):= primitive R u x V+f0 x* mainTerm u R V -- orientation
/-- Multiply by β later; same Layout P & path in input g units, following the FORWARD reset of output step (not recursive Caliber). -/
def forward (f0:ℝ→ℝ)(n: Side)(x:ℝ)(V : Config G n):= beforeLoop R u f0 x V+ ∑ i∈U, charge P f0 i x V
abbrev perceived (U:ℝ→ Config G n→ℝ)(z:ℝ×Stationary.Link G n):=U z.1 (Stationary.input G n z.2)
section algebra
local notation "X"=> Stationary.Link G n
local notation "Π"=> ℝ×X
variable (x:Stationary.Link G n) {f':ℝ×Stationary.Link G n→ℝ} {Λ : Scene G}
include ha
omit [DecidableEq V] in
lemma gradeola (hv:ContDiffAt ℝ ω f' 0)(he:∀ i<2, Radial.jet f' i (1,x)=0)(hr:∀ i≤j,Radial.jet f' (i+2) (1,x)=Λ i n x)(hj: j ≤ t) : Radial.jet (fun z:Π=> f0 z.1*f' z) (j+2) (1,x)=factor p Λ j n x:= by
 let y:Π:=(1,x); let g:=fun (t:ℝ)=> f' (t•y); have hq: ContDiffAt ℝ ω g 0:= ContDiffAt.comp (g:=f') (f:=fun x:ℝ=> x•y) 0 ((zero_smul ℝ y).symm ▸ hv) (contDiffAt_id.smul contDiffAt_const); let f''(z:Π):= f0 z.1*f' z; have heq: (fun z:ℝ=> f'' (z •y))= f0 * g:= by funext a; simp [f'',Prod.smul_mk,y, g];
 have hm : ContDiffAt ℝ ω f'' 0:=(ha.nice.comp (0:Π) contDiffAt_fst).mul hv; rw [← jet_entry (hm.of_le le_top), heq, some_mul ha.nice hq, plus_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Pace.weighs, Finset.sum_apply]; let f (i:ℕ):= (someJ f0 i) * someJ g (j+2-i); change ∑ i∈range (j+2+1),f i= _
 rw [← Finset.sum_subset (s₁:=range (j+1)) (Finset.range_mono (by omega)) (fun i hi he'=>?_)];
 · refine Finset.sum_congr rfl fun i hi=>?_; have hz: i≤ j:= Nat.le_of_lt_succ (mem_range.mp hi); unfold f; rw [ha.writes i (hz.trans hj), show j+2-i=j-i+2 by omega, jet_entry (hv.of_le le_top),hr _ (Nat.sub_le ..)]; rfl
 have hz: j+2-i<2:= by simp only [mem_range, not_lt] at he'; omega
 unfold f; rw [jet_entry (hv.of_le le_top), he _ hz,mul_zero]
include hb
variable (ht:Legal U P) {i:Age} (hi:i∈U)
include ht hi
lemma normalpart : GradeAt 5 (perceived (n:=n) (Floe.sketch P i n)):= by
 let L:=Stationary.arm G n 1; let l:= (ContinuousLinearMap.fst ℝ ℝ X).prod (L.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ ℝ X))
 exact (GradeAt.coarse ((sketch_grade P U (n:=n) ht i hi).lower (by have := i.senior; omega)) (l.contDiff.contDiffAt) l.map_zero)
local notation "f₀"=> charge P f0 i
lemma normcolumn : GradeAt 5 (perceived (n:=n) f₀):= by
 let d (q:ℝ):=(1+f0 q)^(elapsed i); let y:Π → ℝ:=d ∘ Prod.fst -- notation z' invalid
 exact ((GradeAt.unchecked (show ContDiffAt ℝ ω y 0 from (coin_word (elapsed i) ha hb).nice.comp (f:=Prod.fst) (0:Π) contDiffAt_fst)).mul (normalpart P U p ha hb ht hi)) -- arity
lemma char (hh:j ≤ t): Radial.jet (perceived (n:=n) f₀) (j+2) (1,x)=moiety p i P j n x := by
 let f' := perceived (Floe.sketch P i n); let d (p:ℝ):=(1+f0 p)^(elapsed i); have hw:=normalpart P U p ha hb ht hi (n:=n); change Radial.jet (fun z:Π=> d z.1*f' z) (j+2) (1,x)= _; apply gradeola (n:=n) (f':=f') (Λ:=trade i.e (P i)) (ladder (elapsed i) p) (coin_word _ ha hb) x hw.smooth (fun i hi=> hw.jet_z _ (by omega)); swap; exact hh
 intro k hk; obtain ⟨v,c,hC,hp⟩:=ht.rent i hi; let g:=Stationary.turnSeries (P i) (m:=n); have hz:= favor_exp g (Stationary.turns_analytic _ hC hp).contDiffAt 1 x (k+2) i.stamp; have hh:= i.recovery; unfold Haiku.Coat.trade; split
 next he=>
    rw [if_pos (show i.stamp ≤ k+2 from by omega),one_pow,one_mul,show k+2-i.stamp=k-i.e+i.r from (by omega)] at hz; exact hz
 next he=>
    by_cases h:i.stamp ≤ k+2
    · rw [if_pos h,one_pow,one_mul] at hz; apply Eq.trans hz; let f:= Extra.Iteration.Calibration.acted (P i) (n:=n); have hv:= Calibration.acted_jet _ hC hp (n:=n); rw [show Radial.jet g _ _=_ from (jet_continuous_right (Stationary.arm G n 1).toContinuousLinearMap (hv.of_le (show (↑(k+2-i.stamp):WithTop ℕ∞)≤ω from le_top)) x), Comparison.RG02.Assembly.jet, show iteratedFDeriv ℝ (k+2-i.stamp) (Calibration.acted (P i) (n:=n)) 0=0 from lower_jet hC hp _ (by omega)]; simp
    rw [if_neg h] at hz; exact hz
omit ht hi
variable {a L Y:ℝ} (hR:R.Bounds u a L Y)
include hR
local notation "T"=> mainTerm u R
local notation "t'"=> Precision.loop R
local notation "h₀"=> perceived (n:=n) (beforeLoop R u f0)
local notation "Lℓ"=> Stationary.arm G n 1

omit ha hb in
lemma core : GradeAt 2 (T ∘ Stationary.input G n):= by
 let f:=Calibration.main R u (n:=n); let Z:=fieldDir G n 1
 have hy : GradeAt 2 f:= by
    refine ⟨Calibration.main_jet hR,?_⟩; intro i hi; ext1 v; rcases i with _|i
    · rw [iteratedFDeriv_zero_apply, show f 0=0 from (Comparison.RG02.Bulk.main_origin u R hR)]; rfl
    have hh : i=0:= by omega
    subst i
    change (iteratedFDeriv ℝ 1 f 0) v=0; rw [iteratedFDeriv_one_apply, show fderiv ℝ f 0=0 from (Comparison.RG02.Bulk.main_first u R hR)]; rfl
 exact GradeAt.coarse (f:=f) (g:=Lℓ) hy (Lℓ).contDiff.contDiffAt (Lℓ).map_zero
omit ha hb in
lemma cashier : GradeAt 0 (t' ∘ Stationary.input G n):= GradeAt.coarse (f:= Precision.loop (n:=n) R ∘ represent) (g:= Lℓ) (GradeAt.unchecked (Comparison.RG02.Bulk.loop_smooth (m:=n) u R hR)) (Lℓ).contDiff.contDiffAt (Lℓ).map_zero
lemma fever : GradeAt 2 (h₀):= by
 let l:= Prod.snd (α:=ℝ) (β:=X); let Z:= ((T) ∘ Stationary.input G n); let Y:= fun z:Π=>z.1; let g:= (t') ∘ Stationary.input G n; have hz: GradeAt 2 (Z ∘ l):= (core R u hR (n:=n)).coarse contDiffAt_snd rfl; have hm: GradeAt 0 (g ∘ l):= GradeAt.coarse (cashier R u hR) contDiffAt_snd rfl
 exact (hz.add ((GradeAt.shifts Y contDiffAt_fst rfl 2).mul hm)).add ((GradeAt.unchecked (ha.nice.comp (f:=Y) (0:Π) contDiffAt_fst)).mul hz)
lemma schedule (hj:j ≤ t): Radial.jet h₀ (j+2) (1,x)= Pace.shiftB p u R j n x:= by
 let b:= (T) ∘ Stationary.input G n; let g:= t' ∘ Stationary.input G n; let f:= b ∘ Prod.snd (α:=ℝ); let f' (z:Π):=z.1^2 * g z.2; let hL (z:Π):= f0 z.1 * f z;
 have hp:=core R u hR (n:=n); have hh : GradeAt 2 f:= hp.coarse (g:=Prod.snd) contDiffAt_snd rfl; have he:=cashier R u hR (n:=n); have hm: ContDiffAt ℝ ω f' 0:= (contDiffAt_fst.pow _).mul (f:=fun (x:Π)=>x.1^2) (he.smooth.comp (g:=g) (f:=Prod.snd) (0:Π) contDiffAt_snd); have ht: ContDiffAt ℝ ω hL 0:= (ha.nice.comp (f:=Prod.fst) (0:Π) contDiffAt_fst).mul hh.smooth
 have hb(i:ℕ):Radial.jet f (i+2) (1,x)=Pace.base u R i n x:= jet_continuous_right (ContinuousLinearMap.snd ℝ ℝ X) (hp.smooth.of_le (show (↑(i+2):WithTop ℕ∞)≤ω from le_top)) (1,x)
 have hξ : Radial.jet f' (j+2) (1,x)=Haiku.Coat.clerk (fun n=> Precision.loop R) 0 j n x:= by rw [show Radial.jet f' (j+2) (1,x)= _ from favor_exp (g) he.smooth 1 x (j+2) 2, if_pos (by omega), Nat.add_sub_cancel, one_pow,one_mul]; rfl
 change Radial.jet (f+f'+hL) (j+2) (1,x)=_+_; rw [Laplace.jet_add (show ContDiffAt ℝ ω (f+f') 0 from (hh.smooth.add hm)) ht _, show Radial.jet hL (j+2) (1,x)= _ from gradeola (Λ:= Pace.base u R) p ha x hh.smooth (fun i hi=> hh.jet_z _ hi) (fun i _=> hb i) hj, Laplace.jet_add hh.smooth hm _, hb, hξ]; rfl
include ht
lemma vested : GradeAt 2 (perceived (forward R u P U f0 n)):= by
 let g (z:Π):= ∑ i∈U, perceived (n:=n) (charge P f0 i) z
 have hh i (hi:i∈U): GradeAt 2 (perceived (n:=n) (charge P f0 i)):= (normcolumn P U p ha hb ht hi).lower (by decide)
 exact (fever R u p ha hb hR (n:=n)).add (GradeAt.list_sum U _ hh)
lemma profileDatum (hj:j ≤ t): Radial.jet (perceived (forward R u P U f0 n)) (j+2) (1,x)= Pace.grouping p P U u R j n x:= by
 let f(i:Age):= perceived (n:=n) (charge P f0 i); let hG(i:Age)(hi:i∈U):ContDiffAt ℝ ω (f i) 0:=(normcolumn P U p ha hb ht hi).smooth
 have hp: ContDiffAt ℝ ω (∑ i∈U,f i) 0:= (show (fun x=> ∑ i∈U,f i x)=(∑ i∈U,f i) from funext fun x=> (Finset.sum_apply ..).symm) ▸ ContDiffAt.sum hG; have hy (i:X):=(fever R u p ha hb (n:=n) hR).smooth
 have hs:perceived (n:=n) (forward R u P U f0 n)= h₀ + ∑ i∈U,f i:= by funext x; change _= (h₀) x+ _; rw [Finset.sum_apply]; rfl
 rw [hs,Laplace.jet_add (hy x) hp _,goth hG,schedule R u p ha hb x hR hj]; change _ = _ +(∑ i∈U,moiety p i P) j n x; simp_rw [Finset.sum_apply]; exact congr_arg _ (Finset.sum_congr rfl (fun i hi=> char P U p ha hb x ht hi hj))
end algebra

open Wheel Fare ConnectedActivityE6.Coat
variable {β:ℝ} (he:0<β)(hk:0< now p t β)(x:Config G n)
local notation "T[" a "]"=>Coat.gStep a
local notation "t₀"=> now p t β
include he
lemma price_pow (i:Age): Plateau.ratioW (T[β]) i.e i.r=β *(T[β])^i.stamp:= by
 have h:= square_heat he; have hx :0<T[β]:= Fare.gS β he|>.1; have hΞ : (T[β])^i.stamp*(T[β])^i.r= (T[β])^i.e*(T[β])^2:= by rw [←pow_add,←pow_add,← i.recovery];
 unfold Plateau.ratioW; field_simp; linear_combination -β * hΞ - (T[β])^i.e * h
include hk
lemma hed : 0<1+wag p t β:= pos_of_mul_pos_right hk he.le -- maybe left
lemma revealed : β * forward R u P U (PositionX.Jet.delay p t) n T[β] x = now p t β * audition (f:=n) R u P U T[t₀] x:= by -- x used
 have hp i : β * charge P (PositionX.Jet.delay p t) i (T[β]) x= t₀ * sketch P i n T[t₀] x:= by
    let g:=T[β]; let q:=1+wag p t β; let y:=T[t₀]; let f:= Extra.Iteration.action (P i) x; change β*(q^elapsed i*(g^i.stamp * f))=(t₀)*(y^i.stamp*f);
    have he' : Plateau.ratioW y i.e i.r=Pace.cap i g (wag p t β):= by unfold y now; rw [Wheel.Hall.bubble he _ (hed _ he hk)]; exact rhythmic i _ _ (Fare.gS β he|>.1) (hed _ he hk)
    unfold Pace.cap at he'; rw [show Plateau.ratioW y _ _= _ from price_pow hk i, show Plateau.ratioW g _ _= _ from price_pow he i] at he';
    calc
      _ = q^elapsed i*(β *g^i.stamp)*f := by ring
      _ = _ := by rw [show q^elapsed i*(β *g^i.stamp)=(t₀)*((T[t₀])^i.stamp) from he'.symm, mul_assoc]
 let A:= Precision.loop R x; let X:= mainTerm u R x; have ht : β*beforeLoop R u (PositionX.Jet.delay p t) (T[β]) x=t₀* primitive R u T[t₀] x:= by
    have h:= square_heat he; have ha:= square_heat hk; let f:= wag p t β; let z:= T[t₀]; let y:= T[β]; have hv: t₀=β*(1+f):=rfl; change β*(X+y^2*A+f*X)=(t₀)*(X+z^2*A);
    calc
     _ = (t₀)*X+(β*y^2)*A:= by rw [hv]; ring
     _ = _ := by change _= (t₀)*(X+(T[t₀])^2*A); rw [mul_add,mul_left_comm (t₀) ((T[t₀])^2),mul_left_comm ((T[t₀])^2) (t₀), ← mul_assoc (t₀) ((T[t₀])^2), ha, show β*y^2=1 from h]
 change β*(beforeLoop R u (PositionX.Jet.delay p t) (T[β]) x+_)=(t₀)*(primitive R u T[t₀] x+(∑ i∈U, sketch P i n T[t₀]) x); rw [mul_add (t₀), Finset.sum_apply,mul_add β, ht, Finset.mul_sum, Finset.mul_sum]; exact congr_arg (fun c:ℝ=> (t₀)* primitive R u T[t₀] x+c) (Finset.sum_congr rfl fun i hi=> hp i)
end YM.Qlocal.Binding

