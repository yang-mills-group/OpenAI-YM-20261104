import YM.AllOrder.Wheel.Travel
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open Plateau Response
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {ι:Type*}{V:ι→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)][∀ i,FiniteDimensional ℝ (V i)]
variable {T:Clock ι}{p C s ζ b:ι→ℝ}{a c:ℝ}{f g:∀i,V i→ℝ}{x z:∀i,V i}{j l n:ℕ}
local notation "H"=> T.Meter
local notation "ℰ"=> Shellac.off
structure Estate {V:ι→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] (T:Clock ι)(j n:ℕ)(p b:ι→ℝ)(x:∀ i,V i)(f:∀ i,V i→ℝ)(F:∀ i,Book (V i)):Prop where
    trend (l:ℕ) (h:l ≤ n) : Cover T j (graded (l+1)) p (fun i=> ℰ (f i-delay (F i) l (b i))) x
namespace Estate
variable {F G:∀ i,Book (V i)} (h: Estate T j n p b x f F)
local notation "τ"=> Estate T j n p b x
lemma unit (hc:∀ᶠ i in T.rail,0≤p i):τ (fun i=> (0:V i→ℝ)) 0:= by
 refine ⟨fun j hj=>?_⟩; simp_rw [delay,Pi.zero_apply,smul_zero,sum_const_zero,sub_zero]; exact ((Cover.fixed (fun _=> (0:ℝ)) hc (by simp only [norm_zero]; exact Meter.nil T _))|>.home (g:=fun i=>ℰ 0) (Eventually.of_forall fun i=>funext fun x=> by simp [Shellac.off]))
include h
lemma pair (hg:τ g G): τ (f+g) (F+G) := by
 refine ⟨fun l hl=>?_⟩; apply ((h.trend l hl).add (hg.trend l hl)).home; refine Eventually.of_forall fun i=>?_ ; simp only [Pi.add_apply,skirt,off_ya,delay,smul_add,sum_add_distrib]; abel
omit h in
lemma total {α:Type*}{F:α→(i:ι)→ Book (V i)}{f:α→(i:ι)→V i→ℝ}(A:Finset α)(h:∀ i∈A,τ (f i) (F i))(ht:∀ᶠ i in T.rail,0≤p i) : τ (∑ i∈A, f i) (∑ i∈A,F i):= by
 induction A using Finset.induction_on with | empty=> rw [sum_empty,sum_empty]; exact unit ht | insert i A he ih => rw [sum_insert he,sum_insert he]; exact Estate.pair (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma spin (hq:Cover T j 0 p (fun i=> ℰ (f i)) x) (hb:H b (-(1/2))) {a:ι→ℝ}{u:ι→Word ℝ} (hr:TaylorCap T n b a u)(ht:∀ᶠ i in T.rail,0≤p i): τ (fun i=> a i • f i) (fun i=> forming (u i) (F i)):= by
 refine ⟨fun k hk=>?_⟩; let L i:=ℰ (f i); let z i:=delay (u i) k (b i); let G' i:=(a i-z i) • L i; let η (k:ℕ) i:= b i ^ k • u i k; let Q:= range (k+1); let m j i:= η j i • ℰ (f i- delay (F i) (k-j) (b i)); have hm(j₀)(hj:j₀∈Q): Cover T j (graded (k+1)) p (fun i=> m j₀ i) x:= by
    have ht:=mem_range.mp hj; exact ((h.trend (k-j₀) (by omega)).caliber ((hb.pow _).mul (hr.steps j₀ (by omega)))).weak (by unfold graded;push_cast; rw [Nat.cast_sub (by omega : j₀≤k)]; linarith)
 apply (((hq.caliber (hr.stamps k hk)|>.weak (by simp :0+graded (k+1) ≤graded (k+1))).add (Cover.booking Q hm ht))).home; apply Eventually.of_forall; intro i; unfold m η; change (a i- delay (u i) k (b i)) • ℰ (f i) +(∑ j∈range (k+1),(_ * _ :ℝ) • ℰ ((f i) - (_:V i→ℝ)))= _; rw [delay_right (V:=V) (i:=i)]; ext1 x; simp only [Shellac.off,Pi.sub_apply,Pi.add_apply, Pi.smul_apply, Finset.sum_apply,smul_eq_mul]; -- algebra
 let Q₀ l:= (b i)^l *u i l; have hs : delay (u i) k (b i)=∑ i∈Q,Q₀ i:=rfl; rw [hs]
 let v:= f i x; let d:=f i 0; let P l:=delay (F i) (k-l) (b i); change (a i-∑ j∈Q,Q₀ j)*(v-d)+(∑ j∈Q,Q₀ j *(v-P j x- (d-P j 0)))=a i*v-∑ j∈Q,Q₀ j* P j x-(a i*d-∑ j∈Q,Q₀ j* P j 0); simp_rw [mul_sub, Finset.sum_sub_distrib,sub_mul,Finset.sum_mul]; ring
lemma cong (hf:∀ᶠ i in T.rail, ℰ (f i)=ℰ (g i))(he:∀ l≤n, ∀ᶠ i in T.rail,F i l= G i l): τ g G := by
 refine ⟨fun k hk=>?_⟩; apply (h.trend k hk).home; filter_upwards [Eventually.and hf (eventually_all.mpr (show ∀ j:Fin (k+1),∀ᶠ i in T.rail, F i j.val = G i j.val from fun i=>he _ (by have ht:= i.isLt; omega)))] with i hi; have ht:delay (F i) k (b i)=delay (G i) k (b i):= Finset.sum_congr rfl fun a hh => congr_arg (_ • ·) (hi.2 ⟨a,mem_range.mp hh⟩); rw [skirt,skirt,ht,hi.1]
end Estate
end YM.AllOrder.Catch
