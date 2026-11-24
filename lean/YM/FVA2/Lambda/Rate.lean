import YM.FVA2.Lambda.Cent
/-!
# κ-reading values reduced
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Lathe
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Arc MS.Rock MS.Rock.Path MS.Motif MS.Hem MS.Hem.Mell MS.Outlook MS.Halo MS.Alps MS.City MS.Plane.Flux
open MS.Book MS.Book.Convolve MS.Dock MS.Train MS.Emit MS.Garment MS.Pearl
open Canvas (quad high line4 triple upperquad trigger)
open Area Shells Pages
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}
local notation "g☆"=>triple G
local notation "Z"=>Momentum.sq (A:=Axis)
variable (q:QP)(x:ℝ)(i:G.ColorIndex)
variable (h:G.Simple)
local notation "L"=>quad G (melt 0) g☆ g☆
local notation "ℬ"=>line4 G (hot 0)
local notation "A"=>Real.exp
local notation "w"=>pairL (W₀ 1 i) (W₀ 1 i)
local notation "u"=>pairL (C₀ i) (U₀ 0 i)
include h
lemma ℑ : trc ℬ q L ( w (north x) )= (2*(G.casimir:ℂ))*( Lathe.cast (existW ( partQ q ) q) x+ Lathe.cast (existW ( partQ (-q) ) (-q)) x ):= by
    rw [ pairL, cyclic (hot 0) (melt 0) q _ _ ( by simp ) ]; simp_rw [ jelly _ _ _ _ _ _ h, statQ ]; -- η
    unfold Lathe.cast existW; push_cast; ring
lemma ℜ : trc ℬ q L (u (north x))= (2*(G.casimir:ℂ)*I)*(Lathe.cast (existW (bud q) q) x+ Lathe.cast ( existW ( bud (-q) ) (-q) ) x):= by
    unfold pairL Lathe.north; rw [ Area.cyclic _ _ q _ _ (by simp) ]; simp_rw [ bust _ _ _ _ _ x h ]; simp_rw [ show ∀ q:QP,van q (rayC 0 x) 0= _ from fun q=> vaneP q x ]; unfold existW Lathe.cast bud Lathe.north; push_cast; ring
-- symmetry after reading implies factor 2 without splitting or neglecting integrability. 
lemma WW : reading 2 (fun x:ℝ=> trc ℬ q L (w (north x)))= ↑(4*G.casimir*Absorb jewel q):= by
    simp_rw [ ℑ _ _ _ h ]; rw [ read_const, Plane.read_add (f:=Lathe.cast (existW (partQ q) q)) (g:= Lathe.cast (existW (partQ (-q)) (-q))) (Complex.ofRealCLM.contDiff.comp ( ting q ( partQ q ) (part_cont q) )) (Complex.ofRealCLM.contDiff.comp ( ting (-q) (partQ (-q)) (part_cont (-q) ) )), cast_read _ _ ( ting q _ (part_cont q) ), cast_read _ _ ( ting (-q) _ (part_cont _) ), read_P,read_P, gem_neg ]; push_cast; ring
abbrev absorbV (q:QP):= Absorb (fun q _=> Lathe.pulse q) q
lemma CU : reading 1 (fun x:ℝ=> trc ℬ q L (u (north x)))= ↑(4*G.casimir*absorbV q)*I:= by
    simp_rw [ ℜ _ _ _ h ]; rw [ read_const, Plane.read_add (f:=Lathe.cast (existW (bud q) q)) (g:=Lathe.cast (existW (bud (-q)) (-q))) ( Complex.ofRealCLM.contDiff.comp ( ting q _ ( bud_cont q ) ) ) ( Complex.ofRealCLM.contDiff.comp ( ting (-q) _ ( bud_cont _ ) ) ), cast_read _ _ ( ting _ _ ( bud_cont q ) ), cast_read _ _ ( ting _ _ ( bud_cont (-q) ) ),read_Q,read_Q,pulse_neg ]; unfold absorbV; push_cast; ring
variable {X:T ( Flats G )}{Y:T ( Coat G )} (hm : leader G X (gloss (pulseX G)) Y)
include hm
lemma project_w (s:ℝ): torch 2 ( trigger X 2 (s,0) ) ( Canvas.letters i )=4*(G.casimir:ℂ)* (↑(∫ q:QP,Absorb jewel q∂μq):ℂ):= by
    change torch 2 _ ( w ( spray 0 ))=_; rw [Pages.pair _ _ _ hm 2 (by decide) ]; -- read
    have he(q:QP):reading 2 (fun x:ℝ=> trc ℬ q L (w (x • spray 0)))=(↑(4*G.casimir* Absorb jewel q):ℂ):= WW q i h; simp_rw [ he ]; rw [integral_complex_ofReal, integral_const_mul]; push_cast; rfl
lemma project_q (s:ℝ): torch 1 ( trigger X 2 (s,0) ) ( Canvas.ghosts i )=4*(G.casimir:ℂ)*( (↑(∫ q:QP, absorbV q∂μq):ℂ)* I ):= by
    change torch 1 _ (u (spray 0))=_; rw [Pages.pair _ _ _ hm 1 (by decide) ]; have he(q:QP): reading 1 (fun x:ℝ=> trc ℬ q L (u (x • spray 0)))=(↑(4*G.casimir* absorbV q):ℂ)*I:= CU q i h; simp_rw [ he ]; rw [ integral_mul_const, integral_complex_ofReal, integral_const_mul ]; push_cast; ring
end YM.FVA2.Lambda.Lathe
