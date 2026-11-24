import YM.MS.Shine.Pick
import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Mud
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.IsolatedZeros
/-!
# Take jets in Laurent calculation explicitly through analytic representatives

Equality not modulo trace identities restricted to four axes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{b:Bool}{D W:Set ℂ}{R T:ℝ}{c:ℂ}{F H:Mob G}{U:Rip G}{x y:ℂ→ℂ}{f g:ℂ→ Mob G} {k:ℤ} {m n:ℕ}
-- define recursively use F normalization separately
lemma Pick.price (h:Pick n f F): kPrice F:= by induction n generalizing f with| zero=> exact Lift.price h| succ n ih=> obtain ⟨H,_hp,h⟩:= h; exact ih h
lemma Pick.live (h:Pick n f F): Live f:= by cases n with|zero=>exact ⟨_,h⟩|succ n=>obtain ⟨H,hp,h⟩:=h; exact ⟨_,hp⟩
lemma Pick.congr (h:Pick n f F)(he:f=ᶠ[dotty] g): Pick n g F:= by
   induction n generalizing f g with|zero=> exact Lift.congr h he| succ n ih=> obtain ⟨H,hP,h⟩:= h; exact ⟨ _,Lift.congr hP he, ih h (he.mono fun i hi=> congr_arg (fun F=> i⁻¹ • (F-H)) hi)⟩
lemma Pick.unique (h:Pick n f F)(he:Pick n f H): F=H:= by
   induction n generalizing f with| zero=> exact Lift.unique h he| succ n ih=> obtain ⟨F',hP,h⟩:=h; obtain ⟨H',hz,he⟩:=he; exact ih h ( Lift.unique hz hP ▸ he)
lemma Pick.add (h:Pick n f F)(hp:Pick n g H): Pick n (f+g) (F+H):= by induction n generalizing f g with
    | zero=> exact Lift.add h hp
    | succ n ih=>
       obtain ⟨F',hx,h⟩:=h; obtain ⟨H',hz,hp⟩:=hp; refine ⟨_, Lift.add hx hz, Pick.congr (ih h hp) (EventuallyEq.of_eq ?_)⟩; ext; simp only [slip,Pi.add_apply,Pi.sub_apply,Pi.smul_apply]; simp only [smul_eq_mul]; ring
lemma Pick.static (h:Pick n f F)(c:ℂ): Pick n (c • f) (c • F) := by
    induction n generalizing f with
    | zero=> exact Lift.static h c
    | succ n ih=>
       obtain ⟨ A,hA,h⟩:=h; refine ⟨_, Lift.static hA c, Pick.congr (ih h) (EventuallyEq.of_eq ?_)⟩; ext; simp only [slip,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]; ring
lemma Pick.fin (S:Finset I){X:I→ℂ→ Mob G}{u:I→ Mob G}(h:∀ i∈S,Pick n (X i) (u i)) : Pick n (∑ i∈S,X i) (∑ i∈S,u i):= by
    classical
    induction S using Finset.induction with
    | empty=> simp only [Finset.sum_empty]; obtain ⟨F,h⟩:=given (G:=G) Live.zero n; simpa only [zero_smul] using (h.static 0)
    | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact ( h i (by simp)).add (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma Pick.mount (h:Pick n f F)(a:ℂ)(s:ℝ): Pick n (fun i=> plow a s (f i)) (plow a s F):= by
    induction n generalizing f with| zero=> exact Lift.plowX h s a| succ n ih=> obtain ⟨u,hu,h⟩:=h; refine ⟨_, Lift.plowX hu s a, Pick.congr (ih h) (Eventually.of_forall fun i=>?_)⟩; change plower a s (slip f u i)= i⁻¹ • (plower a s (f i)- plower a s u); simp only [slip,map_smul,map_sub]
-- exponential product rule

def charm (n:ℕ)(f:ℂ→ℂ): ℂ:= iteratedDeriv n f 0/(n.factorial:ℂ)
lemma matter (h:Forest (disc R) x)(hr:0<R): AnalyticAt ℂ x 0:= ((show DifferentiableOn ℂ x (disc R) from fun i hi=> (h i hi).differentiableWithinAt)).analyticAt (ball_mem_nhds _ hr)
lemma fs_one (h:Forest (disc R) x)(hr:0<R)(k:ℕ): charm k (dslope x 0)=charm (k+1) x:= by
    let G:=FormalMultilinearSeries.ofScalars ℂ (fun n=>charm n x); let F:=dslope x 0; have H:HasFPowerSeriesAt F G.fslope 0 := (matter h hr).hasFPowerSeriesAt.has_fpower_series_dslope_fslope; let V:=FormalMultilinearSeries.ofScalars ℂ (fun n=>charm n F); have ht : HasFPowerSeriesAt F V 0:= (show AnalyticAt ℂ F 0 from ⟨ _,H⟩).hasFPowerSeriesAt; rw [show charm k _ = V.coeff k from Eq.symm (FormalMultilinearSeries.coeff_ofScalars (p:=fun n=>charm n F)), ht.eq_formalMultilinearSeries H, FormalMultilinearSeries.coeff_fslope,FormalMultilinearSeries.coeff_ofScalars]
lemma Pick.choice (hp:Pick n f F)(h:Hol (disc R) f)(hr:0<R)(w:Legs (Shore G m)): F m w=charm n fun i=> f i m w:= by
    induction n generalizing f with
    | zero=> rw [Lift.unique (f:=f) hp (Lift.trim h hr)]; simp [charm]
    | succ n ih=>
        obtain ⟨H,hA,hp⟩:=hp; rw [Lift.unique hA (Lift.trim h hr)] at hp; rw [← fs_one (h.top _ w) hr]; apply ih _ (HolG h hr); refine hp.congr (dotty_non.mono fun i hi=>?_); unfold slip; rw [hung hi]
lemma charm_mult (h:Forest (disc R) x)(he:Forest (disc R) y)(hr:0<R) (n): charm n (fun i=>x i*y i)=∑ i∈ Finset.range (n+1),charm i x * charm (n-i) y := by
    simp_rw [charm, iteratedDeriv_fun_mul ((matter h hr).contDiffAt) ((matter he hr).contDiffAt),Finset.sum_div]; refine Finset.sum_congr rfl fun i hi=>?_; obtain hv: i≤n := by simpa [Nat.lt_succ_iff] using hi
    have H := Nat.choose_mul_factorial_mul_factorial hv; have hk (n:ℕ): (n.factorial:ℂ)≠0:= by exact_mod_cast Nat.factorial_ne_zero n
    have hm : (n.choose i : ℂ)≠0:= by exact_mod_cast Nat.choose_pos hv|>.ne'
    push_cast [← H]; field_simp [hk i,hk (n-i),hm]
lemma Branding (h:Hol (disc R) f)(hr:0<R)(he:Forest (disc R) x) (n){X:ℕ→ Mob G}(hx:∀ i,Pick i f (X i)): Pick n (x • f) (∑ i∈Finset.range (n+1), charm i x • X (n-i)):= by
    have ht:= h.rate he; obtain ⟨F,hF⟩:= given ⟨_,Lift.trim ht hr⟩ n; suffices he:F= ∑ i∈Finset.range (n+1), charm i x • X (n-i) by rwa [← he]
    funext t w; rw [hF.choice ht hr]; change charm n (fun i=> x i * f i t w)= _; rw [charm_mult he (h.top _ w) hr n, Finset.sum_apply,Finset.sum_apply]; simp_rw [Pi.smul_apply,smul_eq_mul,show ∀ i:ℕ,X i t w=charm i (fun i=>f i t w) from fun i=>(hx i).choice h hr w] -- name he shadowing
lemma Stars (h:Forest (disc R) x)(hr:0<R){X:ℕ→ Mob G}(hx:∀ i,Pick i f (X i)): Pick n (x • f) (∑ i∈Finset.range (n+1), charm i x • X (n-i)):= by
    obtain ⟨u,t,ht,hU,hV,hX⟩:= (show Lift f (X 0) from hx 0); have hp : 0<min R t := lt_min hr ht; exact (Branding (hU.mono (ball_subset_ball (min_le_right ..))) hp (fun i hi=>h i (ball_subset_ball (min_le_left ..) hi)) n (fun i=>(hx i).congr hV.symm)).congr (EventuallyEq.smul (EventuallyEq.refl _ x) hV)
lemma chill (c:ℂ): charm n (fun i=>Complex.exp (c*i))=c^n/(n.factorial:ℂ):= by simp [charm,iteratedDeriv_cexp_const_mul]
end YM.MS.Shine
