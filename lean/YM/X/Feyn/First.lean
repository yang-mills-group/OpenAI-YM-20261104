import YM.X.Feyn.Assemble
/-!
First-order diagram interchangeable with Feynman gauge. Formula in uncomputed vertex Hessians; next compare actual cubes.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set MeasureTheory Gauge Lattice Wilson PertExtension PertExtension.Chart PertExtension.Orb Precision
open Pert.Orb (Potential positiveLinks takeLink wilson)
open Series Series.Radial Series.Tested GaussianScore Gauss
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (he:Even n.val) {i:ℕ}
local notation "E" => Potential G n
local notation "A" => Dir G n
local notation "ν"=> tangent G (Cotree n)

def fry (f:E→ℝ) (i:ℕ) := jet f (i+1) - jet f i * jet (wilson (n:=n) (G:=G)) 3

-- smooth kink

def icing : E →L[ℝ] E→L[ℝ] A := (1/2:ℝ) • ((continuousMultilinearCurryFin1 ℝ E A).toContinuousLinearEquiv.toContinuousLinearMap ∘L (iteratedFDeriv ℝ 2 stem 0).curryLeft)
lemma ices (x:E): icing x x=kink x:= by
   unfold kink icing; congr 1 -- ext
lemma fiscal_deriv (a b:A): fderiv ℝ (jet fiscal 2) a b= score a b:= by
   let q(t:A):= score t t; let r (t:ℝ):= a + t • b; let f:=jet (fiscal (G:=G) (n:=n)) 2
   have he (t:ℝ) : 2*f (r t)= scoreDual (a+t•b) (a+t•b):=(second_jet ..).symm
   have hx x y: scoreDual (G:=G) (n:=n) x y=scoreDual y x := by change score x y=score y x; unfold score; apply congr_arg (fun t:ℝ=> t/2); exact Finset.sum_congr rfl (fun i _=> real_inner_comm ..)
   have hr : HasDerivAt r b 0:= by simpa only [one_smul] using! (((hasDerivAt_id' (0:ℝ)).smul_const b).const_add a)
   have hm : HasDerivAt (fun t=> 2*f (r t)) (2*fderiv ℝ f a b) 0:= (((show HasFDerivAt f (fderiv ℝ f a) (r 0) from (by unfold r; simp only [zero_smul,add_zero]; exact ((Plausible.stamp ..).smooth.differentiable (by simp) a).hasFDerivAt)).comp_hasDerivAt 0 hr).const_mul 2)
   have H := hm; rw [funext he] at H; simp only [map_add,map_smul,LinearMap.smul_apply,LinearMap.add_apply,hx b a,smul_eq_mul] at H
   let T:= hasDerivAt_id' (0:ℝ); have hl:= T.mul_const (scoreDual a b); have hh:= T.mul_const (scoreDual b b)
   have hu:=H.unique ((hl.const_add _).add ((T.mul (hh.const_add _)))) -- inspect
   change fderiv ℝ f a b=scoreDual a b; linarith only [hu]

include he
lemma sweet_cut (g:A→ℝ)(h:Plausible g) : fog (g ∘ cut)= gaussian he g:= by
   let v:=saddle (G:=G) he; let p := pad (G:=G) he; let L:= (cut (G:=G) (n:=n)).toLinearMap
   exact moves cost mist v ν L (tangent_proj _ _ L p (LinearMap.ext (cut_pad he)) (pad_fit he)) h

lemma cooks (x:E) : jet wilson 3 x= jet fiscal 3 (cut x) + (saddle he).P (cut x) (kink x):= by
   rw [show wilson= rwS ∘ positiveLinks from funext overS]; rw [tick_stem he x (f:=rwS) (fun t U=>by simp [rwS,energy_gauge]) fiscal fiscal_smooth.contDiffAt rfl (j:=2) (fun i=> zero_fiscal) 3 (by omega),if_neg (by decide),if_pos (by decide), fiscal_deriv]; rfl
variable {T:ChartRatio G}(R:LocalRatio T) {O: Config G n→ ℝ}
variable (h:ContDiffAt ℝ ω (O ∘ representative) 0)(hO:LocalTest (restrictedO O))(hp:RadialOrder i (O ∘ representative))(hv:GaugeInvariant O)(hg:G.Simple)
include h hO hp hv
lemma market_eq (R' : ChartRatio G) -- trim unused
   (x:E)(k:ℕ)(hk:k ≤ i +1): jet (O ∘ positiveLinks) k x= if k=i then jet (O ∘ representative) i (cut x) else if k=i+1 then jet (O ∘ representative) (i+1) (cut x)+ fderiv ℝ (jet (O ∘ representative) i) (cut x) (kink x) else 0:=
   tick_stem he x hv (O ∘ representative) h rfl (fun j hj=>by exact jets_vanish hO.germ hp hj) k hk

lemma at_market : jet (O ∘ positiveLinks) i=jet (O ∘ representative) i ∘ cut:= by
   funext x; rw [market_eq he h hO hp hv (tray G) _ _ (by omega),if_pos rfl]; rfl
lemma full0 (R:LocalRatio T) : diagonalWith T (restrictedO O) i= fog (jet (O ∘ positiveLinks) i):= by
   rw [at_market he h hO hp hv,sweet_cut he _ (Plausible.stamp _ _)]; have hh:= leading_row (P:=T) R hO hp he; refine hh.trans ?_; unfold gaussian Law.average; simp_rw [saddleLaw he];rfl -- division
include hg
lemma paid_v (L : Module.Dual ℝ E): fog (((jet (O ∘ representative) i) ∘ cut)*(⇑L))=0:= by
   rw [← at_market he h hO hp hv]; apply blank hg _ (Plausible.stamp _ _) _ L; intro u x; apply glob O hv _; refine (ContDiffAt.comp (g:=O ∘ representative) _ ?_ stem_smooth).congr_of_eventuallyEq (on_orbit he hv); rw [stem_zero]; exact h

lemma swap_income : fog (fry (O ∘ positiveLinks) i)= gaussian he (jet (O ∘ representative) (i+1) - jet (O ∘ representative) i * jet fiscal 3):= by
   let X := icing (G:=G) (n:=n); let W:=saddle (G:=G) he; let T:= (cut (G:=G) (n:=n)).toLinearMap; let b:= pad (G:=G) he; let L:= b.toContinuousLinearMap; let p:=O ∘ representative; let q:=O ∘ positiveLinks; let f:= jet p i; let g:=jet p (i+1)-f * jet fiscal 3; have hf : Plausible f:= Plausible.stamp _ _
   have H:L ∘ ebi X=b ∘ ebi X:=rfl; let u:=eTrace X L
   have hu: trace (b ∘ ebi X)=(u : E→ℝ):= by rw [← H]; exact trace_eq X L
   apply Eq.trans (b:=fog (fun x=> g (T x) + (fderiv ℝ f (T x) (ebi X x)- f (T x)*W.P (ebi X x) (T x)))) _ (traverse cost mist W ν T b (LinearMap.ext (fun x=>cut_pad he x)) (pad_fit he) (ebi X) (fun v=>plaus_bi X v) ((ebi_nice X).differentiable (by simp)) f g hf ((Plausible.stamp ..).sub (hf.mul (Plausible.stamp ..))) (by rw [hu];exact Plausible.line _) (by rw [hu]; exact paid_v he h hO hp hv hg u))
   apply congr_arg fog; ext x; simp only [fry,Pi.sub_apply,Pi.mul_apply]; rw [at_market he h hO hp hv,market_eq he h hO hp hv (tray G) x (i+1) le_rfl,if_neg (by omega),if_pos rfl,cooks he];
   change jet p (i+1) (cut x) + _ - f (cut x) * (jet fiscal 3 (cut x) + _) = jet p (i+1) (cut x) - f (cut x)* jet fiscal 3 (cut x)+ (fderiv ℝ f (cut x) (icing x x)- f (cut x)*_); rw [ices,show W.P (ebi X x) (T x)=W.P (T x) (kink x) from (congr_arg (fun u=>W.P u (T x)) (ices x)).trans (W.turns ..)]; dsimp only [p,f,W,T,ContinuousLinearMap.coe_coe]; ring
lemma full1 (R:LocalRatio T): diagonalWith T (restrictedO O) (i+1)= fog (fry (O ∘ positiveLinks) i):= by
   rw [swap_income he h hO hp hv hg]; apply treeOne he R h hO hp; let B:= jet (O ∘ representative) i
   rw [← sweet_cut he _ ((Plausible.stamp _ _).mul (Plausible.stamp _ _))]; let U:= jet (rent (n:=n) T) 1
   let L:= fderiv ℝ (rent (n:=n) T) 0 ∘L cut
   suffices hz: (B*U) ∘ cut = ((B ∘ cut)*(L:E→ℝ)) by rw [show _ = _ from hz]; exact paid_v he h hO hp hv hg L.toLinearMap
   ext1 x; change B (cut x)*U (cut x)= B (cut x)*L x; congr 1; unfold L U jet; rw [iteratedFDeriv_one_apply]; simp
end YM.PositionX.Feyn
