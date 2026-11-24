import YM.GradedFar.Interpose
/-!
# Uniform in profiles, asymptotic in just the actual Coupling

Used for deriving shape prices and transferring signed estimates from grid to continuum.
Checkout with exactly the operands, e.g., use trail and actual t thermometer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open FVA2.GradedFar FVA2.GradedFar.Cart Function Filter Set PowerSeries
open scoped Topology BigOperators Classical
variable {I : Type*} {X : Type*} {L : Filter X} {J : Type*} {t : X → ℝ} {f h : X→I→ℂ} {F H : I→PowerSeries ℂ} {G : Type*} [Norm G]

-- uniform cost functions on index I
structure Pays (u:X→ℝ)(L: Filter X)(f:X→I→G): Prop where
 cost : ∃ C:ℝ,0≤C ∧ ∀ᶠ x in L, ∀ i, ‖f x i‖≤ C*u x
structure Receives (t:X→ℝ)(L:Filter X)(f:X→I→ℂ)(F:I→PowerSeries ℂ): Prop where
 cost : Feasible (fun i=> ofPS (F i)) (fun _=>0)
 good : ∀ p:ℕ, Pays (fun i=> |t i|^(p+1)) L (fun x i=> f x i - crop p (t x) (F i))

variable {u v:X→ℝ}
lemma Pays.tran (p:Pays u L f)(hp:f=ᶠ[L] h): Pays u L h:=by
 obtain ⟨C,hC,h⟩:= p.cost; exact ⟨C,hC,(hp.and h).mono fun i hi=> hi.1 ▸ hi.2⟩
lemma Pays.mono (p:Pays u L f)(hv:∀ᶠ i in L, u i ≤ v i): Pays v L f:=by
 obtain ⟨C,hC,h⟩:= p.cost; exact ⟨C,hC,(hv.and h).mono fun i hi j=> (hi.2 j).trans (mul_le_mul_of_nonneg_left hi.1 hC)⟩
lemma Pays.add (p:Pays u L f)(q:Pays u L h): Pays u L (fun i j=> f i j + h i j):=by
 obtain ⟨C,hC,h⟩:= p.cost; obtain ⟨D,hD,h'⟩:= q.cost; exact ⟨C+D,add_nonneg hC hD,(h.and h').mono fun i hi j=>
   (norm_add_le ..).trans ((add_le_add (hi.1 j) (hi.2 j)).trans_eq (add_mul ..).symm)⟩
lemma Pays.mul (p:Pays u L f)(q:Pays v L h): Pays (fun i=>u i*v i) L (fun i j=> f i j * h i j):=by
 obtain ⟨C,hC,h0⟩:= p.cost; obtain ⟨D,hD,h₁⟩:= q.cost; refine ⟨ C*D,mul_nonneg hC hD,?_⟩; filter_upwards [h0,h₁] with i hv hw j
 rw [norm_mul]; exact (mul_le_mul (hv j) (hw j) (norm_nonneg _) ((norm_nonneg _).trans (hv j))).trans_eq (by ring)
lemma Pays.nil : Pays u L (fun _ (_:I)=> (0:ℂ)):= ⟨ 0,le_rfl, Eventually.of_forall (fun i j=> by simp) ⟩
lemma Pays.neg (p:Pays u L f): Pays u L (fun i j=> -(f i j)):=by obtain ⟨C,hC,h⟩:=p.cost; exact ⟨C,hC,h.mono fun i he j=>by rw [norm_neg]; exact he j⟩
lemma Pays.sum (s:Finset J) {p:J→X→I→ℂ} (h:∀ i∈s,Pays u L (p i)): Pays u L (fun i j=>∑ k∈s,p k i j):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; exact Pays.nil
 | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))

-- helper when charges used across log-path; specializing to zero argument gets bound
lemma no_drag {f:I→ℂ}(hf:Charge (fun _=>0) f): ∃ C:ℝ,0≤C ∧ ∀ i, ‖f i‖ ≤ C:=by
 obtain ⟨C,hC,k,h⟩:= hf; exact ⟨C,hC,fun i=> by simpa using h i⟩
lemma no_drag_always {f:I→ℂ}(hf:Charge (fun _=>0) f): Pays (fun _:X=>1) L (fun _=>f):=by
 obtain ⟨C,hC,h⟩:= no_drag hf; exact ⟨C,hC,Eventually.of_forall (fun i j=> by rw [mul_one]; exact h j)⟩
lemma float {p:ℕ} (hv: Charge (fun _=>0) (fun i=>coeff p (F i))) (hp:Tendsto t L (𝓝 0)):
    Pays (fun _=>1) L (fun x i=> (t x:ℂ)^p*coeff p (F i)):= by
 obtain ⟨C,hC,h⟩:= no_drag hv; refine ⟨C,hC,?_⟩; filter_upwards [(hp.norm.eventually_le_const (by simp:‖(0:ℝ)‖<1))] with x hx i
 rw [norm_mul,norm_pow,Complex.norm_real, mul_one]; exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hx) (h i) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)
variable (hp:Tendsto t L (𝓝 0))
include hp in
lemma justified (p:ℕ) (h:Feasible (fun i=> ofPS (F i)) (fun _=>0)): Pays (fun _=>1) L (fun x i=> crop p (t x) (F i)):=by
 simp_rw [crop_eq]; exact Pays.sum _ (fun k _=> float (F:=F) (h k) hp)
include hp in
lemma omissions (p:ℕ)(hf:Feasible (fun i=> ofPS (F i)) (fun _=>0))(hh:Feasible (fun i=> ofPS (H i)) (fun _=>0)):
    Pays (fun x=> |t x|^(p+1)) L (fun x i=> crop p (t x) (F i) * crop p (t x) (H i) - crop p (t x) (F i*H i)):=by
 -- skipped terms degree≥p+1 with bounded multiplier
 have hk (q:ℕ)(A:I→ℂ)(h: Charge (fun _=>0) A): Pays (fun _=>1) L (fun x i=> (t x:ℂ)^q*A i):=by
   obtain ⟨C,hC,h⟩:= no_drag h; refine ⟨C,hC,?_⟩; filter_upwards [hp.norm.eventually_le_const (by simp:‖(0:ℝ)‖<1)] with x hx i
   rw [norm_mul,norm_pow, Complex.norm_real,mul_one]; exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) hx) (h i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
 simp_rw [separate, add_sub_cancel_left]; obtain h : Pays (fun _:X=>1) L (fun x i=>overrun p (t x) (F i) (H i)):=
     Pays.sum _ (fun w _=> hk _ _ ((hf w.1).mul (hh w.2)))
 obtain he:= (show Pays (fun x=> |t x|^(p+1)) L (fun x (_:I)=> (t x:ℂ)^(p+1)) from
    ⟨1,zero_le_one,Eventually.of_forall fun x _=>by rw [one_mul,norm_pow,Complex.norm_real, Real.norm_eq_abs]⟩).mul h
 simpa only [mul_one] using he
lemma cost_const {x:I→ℂ}(h:Charge (fun _=>0) x): Feasible (fun i=> ofPS (PowerSeries.C (x i))) (fun _=>0):= by
 intro k; unfold ofPS; simp only [coeff_C]; split; exact h; exact Charge.const _
lemma constant_crop (p:ℕ)(t:ℝ)(x:ℂ): crop p t (PowerSeries.C x)=x:= by
 rw [crop_eq,Finset.sum_eq_single 0]; simp; exacts [fun i _ hi=> by rw [coeff_C,if_neg hi,mul_zero],by simp]
namespace Receives
lemma congr (p:Receives t L f F)(hv:f=ᶠ[L] h)(he:∀ i,F i=H i): Receives t L h H:=by
 refine ⟨fun i=>?_,fun i=>?_⟩
 · simp_rw [← he]; exact p.cost i
 simp_rw [← he]; exact (p.good i).tran (hv.mono (fun a ha=> by simp_rw [ha]))
lemma bounded (p:Receives t L f F)(hp:Tendsto t L (𝓝 0)) : Pays (fun _=>1) L f:=by
 obtain hq := p.good 0; exact ((hq.mono ((hp.abs.eventually_le_const (by simp : |(0:ℝ)|<1)).mono (fun i hi=> by simpa using hi))).add
   (justified hp 0 p.cost)).tran (Eventually.of_forall (fun i=> funext (fun j=> sub_add_cancel ..)))
lemma const {x:I→ℂ}(h:Charge (fun _=>0) x) : Receives t L (fun _=>x) (fun i=> PowerSeries.C (x i)):= by
 refine ⟨cost_const h,fun _=>?_⟩; simp_rw [constant_crop,sub_self]; exact Pays.nil
lemma fix (x:ℂ): Receives t L (fun _ (_:I)=>x) (fun _=>PowerSeries.C x):= Receives.const (Charge.const x)
lemma add (hA:Receives t L f F)(hB:Receives t L h H): Receives t L (fun x i=> f x i + h x i) (fun i=> F i + H i):=by
 refine ⟨fun i=>?_,fun i=>?_⟩
 · simp_rw [ofPS,map_add]; exact (hA.cost i).add (hB.cost i)
 simp_rw [map_add]; exact ((hA.good i).add (hB.good i)).tran (Eventually.of_forall (fun x=> funext (fun j=> by dsimp only; abel)))
lemma neg (hA: Receives t L f F): Receives t L (fun x i=> -f x i) (fun i=> -F i):=by
 refine ⟨fun i=>?_,fun i=>?_⟩
 · simp_rw [ofPS,map_neg]; exact (hA.cost i).neg
 simp_rw [map_neg]; exact (hA.good i).neg.tran (Eventually.of_forall fun x=> funext fun j=> by dsimp only; abel)
lemma sub (hA:Receives t L f F)(hB:Receives t L h H): Receives t L (fun x i=> f x i - h x i) (fun i=> F i-H i):= by
 simpa only [sub_eq_add_neg] using hA.add hB.neg
lemma mul (hA:Receives t L f F)(hB:Receives t L h H)(hp:Tendsto t L (𝓝 0)): Receives t L
    (fun x i=>f x i*h x i) (fun i=>F i*H i):=by
 refine ⟨fun i=>?_,fun i=>?_⟩
 · simp_rw [ofPS,coeff_mul]; exact Charge.sum _ fun j _=> (hA.cost _).mul (hB.cost _)
 obtain hu:= (hA.good i).mul (hB.bounded hp); obtain hv:= (justified hp i hA.cost).mul (hB.good i)
 simp_rw [mul_one] at hu; simp_rw [one_mul] at hv; exact ((hu.add hv).add (omissions hp i hA.cost hB.cost)).tran (Eventually.of_forall
   (fun x=> funext (fun j=> by ring)))
lemma sum (p: Finset J){f:J→X→I→ℂ} {F:J→I→PowerSeries ℂ} (h:∀ j∈p,Receives t L (f j) (F j)) : Receives t L (fun x i=>∑ j∈p,f j x i) (fun i=>∑ j∈p,F j i):=by
 induction p using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; simpa only [map_zero] using (Receives.fix (I:=I) (t:=t) (L:=L) 0)
 | insert i p hi ih=> simp_rw [Finset.sum_insert hi]; exact (h _ (Finset.mem_insert_self ..)).add (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma prod (p: Finset J) {f:J→X→I→ℂ}{F:J→I→PowerSeries ℂ}(h:∀ j∈p,Receives t L (f j) (F j))(hp:Tendsto t L (𝓝 0)): Receives t L (fun x i=>∏ j∈p,f j x i) (fun i=>∏ j∈p,F j i):=by
 induction p using Finset.induction_on with
 | empty=> simp only [Finset.prod_empty]; simpa only [map_one] using (Receives.fix (I:=I) (t:=t) (L:=L) 1)
 | insert i p hi ih=> simp_rw [Finset.prod_insert hi]; exact (h _ (Finset.mem_insert_self ..)).mul (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj)) hp
lemma along (hA: Receives t L f F)(u:J→I): Receives t L (fun x i=> f x (u i)) (fun i=> F (u i)):=by
 refine ⟨fun i=>?_,fun i=>?_⟩
 · obtain ⟨C,hC,h⟩:= no_drag (hA.cost i); exact Charge.cap ⟨C, fun j=> h (u j)⟩
 obtain ⟨C,hC,h⟩:=(hA.good i).cost; exact ⟨C,hC,h.mono fun x h i=> h (u i)⟩
end Receives
end YM.Integration.GradedFar
