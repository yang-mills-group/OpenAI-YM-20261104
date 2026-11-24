import YM.Qlocal.Quipu.Eluder
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
-- extend wall across both legs. χ preserves quiet.𝒮
variable (x:rule ι n)(o:α→Site n) (Z:R.Mode)
namespace Tender
variable {f g:rule (ι⊕α) n→ℝ}
abbrev sailor (α ι:Type)(n:Side)[Fintype α][Fintype ι]: Prod (rule ι n) (rule α n) ≃L[ℝ] rule (ι⊕α) n:= (desks ι α n).symm
abbrev safe : A →L[ℝ] E:= (sailor α ι n).toContinuousLinearMap ∘L ContinuousLinearMap.inl ℝ _ _
local notation "Z0"=> (safe (ι:=ι) (α:=α) (n:=n))
local notation "B0"=> (sailor α ι n)
local notation "Q"=> Eluder.χ R x o
local notation "T"=> wall Q
omit [DecidableEq α] in
lemma forage : ‖safe (α:=α) (n:=n) x‖ ≤ ‖x‖ := by apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro u; rcases u with ⟨i,u|u⟩; exact norm_le_pi_norm x ..; change ‖(0:ℝ)‖ ≤ _; rw [norm_zero]; apply norm_nonneg
include R in
lemma spacer (F : E→ℝ)(hf:Plausible F): (wall (Eluder.χ R x o) F) = wall (viewed R o) (F ∘ mingle x):= by
 obtain ⟨p,hv⟩:= sold hf; rw [← hv]; have hP (p:Ch (Leaf n (ι⊕α))) : Plausible (guide p ∘ mingle x):= by
    let v:B→L[ℝ] E:= (B0).toContinuousLinearMap ∘L ContinuousLinearMap.inr ..; let w:E:=safe x; have he : (guide p ∘ mingle x)= (fun u=> guide p (w+v u)):= by ext1 t; rw [Function.comp_apply]; apply congr_arg; rw [show w+v t=sailor α ι n (x,0)+sailor α ι n (0,t) from rfl,←(B0).map_add]; simp; rfl
    rw [he]; exact nearStep («B»:=v.toLinearMap) w (bill ..)
 clear hv; induction p using MvPolynomial.induction_on with
 | C v=> rw [guide_const, sky_c]; exact (sky_c ..).symm
 | add p q hp hq=>rw [guide_add,pours_a _ (bill p) (bill q),hp,hq]; exact (pours_a _ (hP p) (hP q)).symm
 | mul_X p i hp=> rw [guide_mul,pours_m _ (bill p) (bill ..), hp]; change _=wall (viewed R o) ((guide p ∘ mingle x)*(guide (MvPolynomial.X i) ∘ mingle x)); rw [pours_m _ (hP _) (hP _), guide_col, sky_x]; rcases i with ⟨z,u|u⟩; exact (congr_arg (_ * ·) (sky_c (viewed R o) (x (z,u)))).symm; exact (congr_arg (_ * ·) (sky_x (viewed R o) (z,u))).symm
-- proj full.Real Price. 
abbrev crystal (R:Marker.Census α)(Z:R.Mode)(o:α→Site n)(F:E→ℝ) := fun x: A=> ((wall (Eluder.χ R x o) F).part Z).re
local notation "Ψ"=> crystal R Z o
local notation "Z'"=> Z.val
variable (i:ℕ) (w:α)
lemma reduced_size (hx:w∈Z.val): (away Z w).val.card=Z.val.card-1:= by rw [show (away Z w).val= Z.val \ {w} from rfl, Finset.sdiff_singleton_eq_erase, card_erase_of_mem hx] -- arguments implicit 
variable (hP:Z.val.card=i)
include hP
private lemma monochrome (hf:Plausible f) : (T f).part Z=((Ψ f x):ℂ):= by
 induction i generalizing Z f with
 | zero=> have he:Z=R.quiet:=Subtype.ext (card_eq_zero.mp hP); rw [he,crystal,money x o hf]; simp
 | succ i ih=>
    have hx:= Finset.card_pos.mp (show 0 < Z.val.card from (hP.symm ▸ i.zero_lt_succ)); let w:= Classical.choose hx; have hl:=Classical.choose_spec hx; have hr: (away Z w).val.card=i:= by rw [reduced_size Z w hl,hP,Nat.add_sub_cancel]
    rw [crystal,Eluder.owns x o w hf Z hl]; exact ih _ hr (hf.ds _)
noncomputable def inst (n k:ℕ):ℝ:= match n with
 | 0 => 1
 | n+1=> honor k * inst n (k-1)
private lemma renting (h:Prices k a f): Prices (k-i) (a*inst i k) (crystal R Z o f):= by
 induction i generalizing Z k a f with
 | zero=>
    have he : Z=R.quiet:= Subtype.ext (card_eq_zero.mp hP); have hx y : crystal R R.quiet o f y = f (Z0 y):= by rw [crystal,money y o h.2.1.read, Complex.ofReal_re]; rfl
    rw [he,funext hx,Nat.sub_zero,inst,mul_one]; refine ⟨h.1,h.2.1.lead Z0,fun x=> (h.2.2 _).trans ?_⟩; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (forage (α:=α) x) _) _) h.1 -- add left actually? add_left old?
 | succ i ih=>
    have hx:= Finset.card_pos.mp (show 0 < Z.val.card from (hP.symm ▸ i.zero_lt_succ)); let w:= Classical.choose hx; have hl:=Classical.choose_spec hx; have hr: (away Z w).val.card=i:= by rw [reduced_size Z w hl,hP,Nat.add_sub_cancel]
    let g:= diff' (bolt (loc ι o w)) f
    rw [show crystal R Z o f= crystal R (away Z w) o g from funext fun x=> congr_arg (Complex.re) (Eluder.owns x o w h.2.1.read Z hl), show k-(i+1)=k-1-i from (by omega), inst,← mul_assoc]; exact ih _ hr (h.taper _ (norm_bolt ..|>.le))
omit hP
lemma hue (hf:Plausible f): (T f).part Z= (crystal R Z o f x:ℂ):= monochrome x o Z _ rfl hf
lemma charged (h:Prices k a f): Prices (k-Z.val.card) (a*inst Z.val.card k) (Ψ f):= renting o Z _ rfl h
lemma valid (s k:ℕ): 0< inst s k:= by induction s generalizing k with | zero=> exact zero_lt_one | succ s ih=> exact mul_pos (honor_pos k) (ih _)
local notation "u"=> Eluder.χ R x o
protected lemma coin (k:ℕ): LinTest E k (fun f=> Ψ f x):= by apply talent (u) ((Complex.reCLM.toLinearMap) ∘ₗ ((Poly.get Z).restrictScalars ℝ).toLinearMap) k
lemma tackle (hf:Plausible f)(hg:Plausible g): crystal R Z o (f-g) = crystal R Z o f-crystal R Z o g:= by ext x; change _= ((wall (Eluder.χ R x o) f).part Z).re- _; unfold crystal; rw [sub_eq_add_neg f,← neg_one_smul ℝ g, pours_a (Eluder.χ R x o) hf (hg.scale _), pours_s _ hg, neg_one_smul, ← sub_eq_add_neg]; exact Complex.sub_re .. -- Poly.part_sub?
end Tender
end YM.Qlocal.Quipu.Eluder

