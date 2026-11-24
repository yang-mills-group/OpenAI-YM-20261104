import YM.X.Site.Rise
import YM.X.Haze.Voucher
/-!
# Visa arithmetic for centered polynomials and their Taylor remainders.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze Finset
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d:ℕ} {G:Gauge} {R:ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=>epsilon q
variable {V:Type} [NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
lemma day_add (p q:Cover): day (p+q) ≤ day p * day q:= by
   unfold day; apply le_trans (b:=(1:ℝ)+(street p+street q:ℕ)) (by exact_mod_cast Nat.add_le_add_left (street_triangle p q) 1) ?_; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (street p),Nat.cast_nonneg (α:=ℝ) (street q)]
def pace (b : Bool) (z:Cover):Cover:= if b then z else 0
lemma day_pace (b:Bool)(z:Cover): day (pace b z)≤day z:= by cases b<;> simp [pace,day,empty_road]
lemma road_pace (b:Bool)(z:Cover): street (pace b z)≤street z:= by cases b<;> simp [pace,empty_road]
def pacer (b:Bool)(x:E4):= if b then x else 0
lemma pace_norm (b:Bool)(x:E4):‖pacer b x‖≤‖x‖:=by cases b<;> simp [pacer]
variable (b: Bool)
include hq in
lemma pace_shift {x:E4}{v:Fielding.Walk}(hz:plot q v x)(p:Cover): plot q (fun i=> pace b (v i)+p) (pacer b x):= by
   cases b
   · simp only [pace, Bool.false_eq_true,↓reduceIte,pacer,zero_add]; exact plot.constant hq p
   simp only [pacer,pace,↓reduceIte]; rw [← add_zero x]; exact hz.add (plot.constant hq p)
include hq in
lemma OnStreet.at_pos (p:Cover)(hr:R≥0){T:ℝ}(ht:T>R){f:Mist V}{c:ℕ→ℝ}(h:OnStreet (gate q T) c n f): OnStreet (gate q R) c n (fun i z=> f i (pace b z+p)):= by
   obtain ⟨C,hc,hh⟩:= h; refine ⟨C*day p^n,by have :=day_pos p; positivity,?_⟩; filter_upwards [hh, gate_shift hq _ _ ht hr p] with i hi hx z hz; replace hu:= hi (pace b z+p) (hx _ ((road_pace b z).trans hz)); apply le_trans hu
   have he: day (pace b z+p)≤ day z*day p:= (day_add _ p).trans (mul_le_mul_of_nonneg_right (day_pace b z) (day_pos p|>.le)); grw [pow_le_pow_left₀ (day_pos _|>.le) he]; rw [mul_pow]; ring_nf; exact le_rfl -- ring cast

-- varying symmetric tensor values
open Tensor
variable {P:ℕ→ T E4 V n}
lemma tensor_visa (h:Released P)(hp:∀ i,Tensor.Sym (P i))(x:E4)(r:ℕ→ℕ): OnStreet r (fun _=>1) n (fun i=> reach x (P i)):= by
   induction n generalizing x with
   | zero=> simp_rw [reach0 _ x Fin.elim0] ; apply Reed.OnStreet.constant; exact (Released.lin ((LinearMap.proj (0:Cover)) ∘ₗ reach x) h).old.congr_left (f₂:=fun i=> P i Fin.elim0) (fun i=> congr_fun (reach0 (P i) x Fin.elim0) 0) -- usage lm instances
   | succ n IH=> refine Reed.OnStreet.of_step ?_ ?_; have ht : Released (fun i=>reach x (P i) 0) := Released.lin ((LinearMap.proj (0:Cover): (Cover→ V)→ₗ[ℝ] V) ∘ₗ reach (V:=V) (n:=n+1) x) h; exact ht.old; 
                  intro i;  simp_rw [step_grabs (hp _)]; exact IH (P:=fun i'=> burst i (P i')) (show Released (fun i'=> burst i (P i')) from Released.lin (burst (V:=V) (n:=n) i) h) (fun u=> burst_sym (hp _) i) _
include hq in
lemma tensor_earn (h:Released P)(x:E4){f:Fielding.Walk}{y:E4}(hp:plot q f y): Released (fun i=> ε i ^ n • reach x (P i) (f i)):= by
   let β:= Module.finBasis ℝ (T E4 V n); let D:= Fin (Module.finrank ℝ (T E4 V n)); let F(v:D)(i:ℕ):= ε i ^ n • reach x (β v) (f i)
   have he : Tendsto (fun i=> ε i • (mapZ (f i)+x)) atTop (𝓝 y):= by simp_rw [smul_add]; simpa only [zero_smul,add_zero] using! (Tendsto.add hp ((paths hq).cutoff.smul_const x)) -- wrong spot
   have hf (i): ε i ^ n • reach x (P i) (f i)=∑ v:D,(β.coord v (P i)) • F v i:= by nth_rw 1 [← β.sum_repr (P i)]; rw [map_sum,Finset.sum_apply, Finset.smul_sum]; refine sum_congr rfl (fun v _=>?_); rw [map_smul,Pi.smul_apply]; exact smul_comm ..
   simp_rw [hf]; apply Released.sumR; intro v _; refine Released.smul ⟨diagonal (β v) y, ?_⟩ (Released.lin (β.coord v) h); exact twig (paths hq).cutoff he _
lemma burst_jumps (n m:ℕ)(h:m≤n)(l:Fin m→Axis)(x:E4)(P:ℕ→ T E4 V n) (hp:Released P)(hv:∀ i,Tensor.Sym (P i)): ∃ y:E4,∃ Q : ℕ→T E4 V (n-m), Released Q ∧ (∀ i, Tensor.Sym (Q i)) ∧ ∀ i:ℕ, jumped l (reach x (P i))=reach y (Q i):= by
   induction m generalizing n x with
   | zero=> exact ⟨x,P,hp,hv,fun i=> rfl⟩
   | succ m IH=> cases n with | zero=> omega| succ n=>
     let j:=l 0; let z:=x+tip j; let Q:= (fun i=> burst j (P i)); obtain ⟨y,V,p,hf,ht⟩:= IH n (by omega) (Fin.tail l) z Q (show Released Q from by unfold Q; exact Released.lin (burst j) hp) (fun i=> burst_sym (hv i) j)
     -- subst nat shift cast
     have he (i:ℕ): jumped l (reach x (P i))=reach y (V i):= by rw [jumpIt,jumps,step_grabs (hv i)]; exact ht i
     generalize hk:n+1-(m+1)=k; have hu:k=n-m:=by omega
     clear hk; subst k; exact ⟨y,V,p,hf,he⟩
include hq in
lemma burst_result (hr:0 ≤ R)(hm:m≤n)(l:Fin m→Axis)(x:E4)(p:Cover)(hp:Released P)(hs:∀ i,Tensor.Sym (P i)): Visa q R 0 ((n-m:ℕ):ℤ) (fun i z=> jumped l (reach x (P i)) (pace b z+p)):= by
   obtain ⟨y,V,h,hV,he⟩:= burst_jumps n m hm l x P hp hs; simp_rw [he]; refine ⟨?_,fun x hx hr z hz=>?_⟩
   · obtain ⟨C,hc,hi⟩:= OnStreet.at_pos hq b p hr (lt_add_one R) (tensor_visa h hV y (gate q (R+1))); exact ⟨C,hc,(by simpa only [price,zpow_natCast,zpow_zero,norm_one,one_mul] using hi)⟩
   rw [sub_zero]; simp only [zpow_natCast]; exact tensor_earn hq h y (pace_shift hq b hz p)
end YM.PositionX.Clove
