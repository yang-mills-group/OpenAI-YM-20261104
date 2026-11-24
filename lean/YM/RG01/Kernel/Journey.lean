import YM.RG01.Kernel.Ratio
import YM.Next.WARD_BIN.Lies
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Kernel
open Function Filter Set MeasureTheory Complex Metric Topology Finset Lattice RG Wilson Matrix
open ConnectedActivityE6.Blaze Brush WardBin.Lies
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c: Side}{n k:ℕ}
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D][NormedSpace ℝ D]{x:E}{C p:ℝ}(f:E→G.Mat)
-- helper linear translation
lemma morph {f:E→D}{F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F](H : Brush k C p f x)(L:D→L[ℝ] F)(v:ℝ)(h:‖L‖≤v):
    Brush k (v*C) p (fun i=>L (f i)) x:=by
  refine ⟨L.contDiff.contDiffAt.comp _ H.smooth,H.pos,fun i hi=> (L.norm_iteratedFDeriv_comp_left H.smooth (Nat.cast_le.mpr hi)).trans ?_⟩
  rw [mul_assoc]; exact mul_le_mul h (H.order i hi) (norm_nonneg _) ((norm_nonneg _).trans h)

-- matrix → explicit angle spaces. continuity via finite dim; avoid topological defeq issue by mkContinuous and explicit K compactness on Frobenius unit. Use generic morph via linear transform with `let h := ...` specifying TopologicalSpace (Matrix...)
section changeTopology
local instance frobT {m n:Type*}[Fintype m][Fintype n] : TopologicalSpace (Matrix m n ℂ):= PseudoMetricSpace.toUniformSpace.toTopologicalSpace

def entryMap (G:Gauge):G.Mat→L[ℝ] Block G:= LinearMap.toContinuousLinearMap {toFun:=array,map_add' _ _:=rfl,map_smul' _ _:=rfl}
def starEntryMap (G:Gauge):G.Mat→L[ℝ] Block G:= LinearMap.toContinuousLinearMap {toFun:=fun m=>array (star m),map_add' a b:=by rw [star_add];rfl,map_smul' a b:=by rw [star_smul];simp; rfl}
-- use only Brush theorem downstream (do not rely on instance resolution on these CLs)
def visa (G:Gauge):= max (1:ℝ) (max ‖entryMap G‖ ‖starEntryMap G‖)
lemma visa_one : 1 ≤ visa G:=le_max_left ..
lemma entrybrush (hf:Brush k C p f x) : Brush k (visa G*C) p (fun i=>array (f i)) x ∧ Brush k (visa G*C) p (fun i=>array (star (f i))) x := ⟨morph hf (entryMap G) (visa G) ((le_max_left ..).trans (le_max_right ..)),morph hf (starEntryMap G) (visa G) ((le_max_right ..).trans (le_max_right ..))⟩
end changeTopology

-- price path for any Fin family via recursion keeping t ambient variables.
private lemma expIncome (G:Gauge)(n:ℕ): ∃ h:ℝ, 1≤h∧Brush n h 1 (fun i=>G.mat (G.lieExp i)) 0 := by
  obtain ⟨C,h,hP⟩:= Brush.neighborhood (k:=n) 0 (G.exp_jet.contDiffAt.of_le le_top)
  exact ⟨max 1 C,le_max_left ..,(hP.self_of_nhds).climb (le_max_right ..) le_rfl⟩
def expSeal (G:Gauge) (n:ℕ):ℝ:= n.factorial*(expIncome G n).choose
lemma seal_one (G:Gauge) (n:ℕ): 1 ≤ expSeal G n:=one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1≤ n.factorial from Nat.factorial_pos _)) ((expIncome G n).choose_spec.1)


def steps (M:List (D→L[ℝ] G.Color)) (x:D)(u:G.El): G.El:= List.foldl (fun u A=>G.lieExp (A x)*u) u M

lemma anglePay (M:List (E→L[ℝ] G.Color))(e:ℝ)(he:0≤e)(h:∀ i∈M, ‖i‖≤e)(u:G.El)(k:ℕ):
    Brush k ((expSeal G k)^M.length*‖G.mat u‖) (2*e*M.length) (fun x=> G.mat (steps M x u)) (0:E):= by
  induction M using List.reverseRecOn with
  | nil => simpa only [steps,List.foldl_nil,List.length_nil,Nat.cast_zero,pow_zero,one_mul,mul_zero] using Brush.certified (k:=k) (x:=(0:E)) (le_refl 0) (G.mat u)
  | append_singleton l A hL=>
    have hl:= hL (fun i hi=> h _ (List.mem_append_left _ hi))
    have hA:Brush k 1 e A (0:E):= Brush.linearB A (by rw [map_zero,norm_zero]; norm_num) (by rw [one_mul]; exact h _ (by simp)) he
    have ha:Brush k (expSeal G k) (2*e) (fun x=>G.mat (G.lieExp (A x))) 0:=by
      have hp:Brush k (expIncome G k).choose 1 (fun i=>G.mat (G.lieExp i)) (A 0):=by rw [map_zero]; exact (expIncome G k).choose_spec.2
      rw [show (2:ℝ)=1+1 by norm_num]; exact hA.pine hp
    have hh:= ha.paints hl
    rw [List.length_append,List.length_singleton,pow_succ']
    simp_rw [steps,List.foldl_append,List.foldl_cons,List.foldl_nil,G.mat_mul]
    rw [mul_assoc (expSeal G k),(by push_cast; ring : 2*e*((l.length+1:ℕ):ℝ) = 2*e+2*e*(l.length:ℝ))]
    exact hh

lemma steps_zero (M:List (E→L[ℝ] G.Color))(u:G.El):steps M 0 u=u:= by induction M generalizing u with | nil=>rfl | cons i M h=>change steps M 0 (G.lieExp (i 0)*u)=u; simp [h]

-- Generic product and Pi targets through restriction.Linear maps cash op norm at probability rate.
lemma both {f:E→D}{g:E→D}(hf:Brush k C p f x)(hg:Brush k C p g x): Brush k C p (fun i=>(f i,g i)) x:=by
  have he:=hf.smooth.prodMk hg.smooth
  refine ⟨he,hf.pos,fun i hi=>ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hf.nonneg (pow_nonneg hf.pos i)) fun v =>?_⟩
  let L: E→D×D:= fun i=> (f i,g i)
  have h (T:D×D→L[ℝ]D) : T (iteratedFDeriv ℝ i L x v) = iteratedFDeriv ℝ i (T ∘ L) x v:= by rw [T.iteratedFDeriv_comp_left he (by exact_mod_cast hi)]; rfl
  rw [Prod.norm_def]; refine max_le ?_ ?_
  · change ‖ContinuousLinearMap.fst ℝ D D (iteratedFDeriv ℝ i L x v)‖≤_; rw [h]
    exact ((iteratedFDeriv ℝ i f x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hf.order _ hi) (Finset.prod_nonneg fun _ _=> norm_nonneg _))
  change ‖ContinuousLinearMap.snd ℝ D D (iteratedFDeriv ℝ i L x v)‖≤_; rw [h]
  exact ((iteratedFDeriv ℝ i g x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hg.order _ hi) (Finset.prod_nonneg fun _ _=> norm_nonneg _))
lemma all {ι:Type*}[Fintype ι][Nonempty ι]{f:ι→E→D}(hf:∀ i,Brush k C p (f i) x): Brush k C p (fun z i=> f i z) x:=by
  let L:E→ι→D:=fun i j=>f j i
  have he:ContDiffAt ℝ (↑k) L x:= contDiffAt_pi.mpr fun i=>(hf i).smooth
  let i:ι:=Classical.choice ‹_›
  refine ⟨he,(hf i).pos,fun j hj=>ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (hf i).nonneg (pow_nonneg (hf i).pos j)) fun v=>?_⟩
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (hf i).nonneg (pow_nonneg (hf i).pos _)) (Finset.prod_nonneg fun _ _=> norm_nonneg _))).mpr
  intro i
  let X:(ι→D)→L[ℝ] D:= ContinuousLinearMap.proj i
  have h : X (iteratedFDeriv ℝ j L x v) = iteratedFDeriv ℝ j (X ∘ L) x v:=by rw [X.iteratedFDeriv_comp_left he (by exact_mod_cast hj)]; rfl
  change ‖X (iteratedFDeriv ℝ j L x v)‖ ≤ _; rw [h]
  exact ((iteratedFDeriv ℝ j (f i) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right ((hf i).order _ hj) (Finset.prod_nonneg fun _ _=>norm_nonneg _))

abbrev peel (M:G.El):Pair G:= (array (G.mat M - 1),array (star (G.mat M-1)))
def saved (k n:ℕ)(G:Gauge) := (visa G * ((expSeal G k)^n * ‖(1:G.Mat)‖+‖(1:G.Mat)‖))
lemma peeling (M: List (E→L[ℝ] G.Color))(e : ℝ) (k:ℕ) (he:0 ≤ e) (hM:∀ i∈M, ‖i‖ ≤ e):
    Brush k (saved k M.length G) (2*e*M.length) (fun x=> peel (steps M x 1)) 0:=by
  have hf := anglePay M e he hM (1:G.El) k; rw [G.mat_one] at hf
  let p (x:E):= G.mat (steps M x 1)-1
  have hx := entrybrush p (hf.separating (Brush.certified (d:=2*e* M.length) (by positivity) (1:G.Mat)))
  exact both hx.1 hx.2
lemma scaled (M:List (E→L[ℝ] G.Color))(e:ℝ)(k:ℕ)(he:0 ≤ e)(h:e≤1)(hM:∀ i∈M,‖i‖≤e):
    Brush k (saved k M.length G) (2*M.length) (fun x : E=> e⁻¹ • peel (steps M x 1)) 0:=by
  have hf:= (peeling M e k he hM); let f:= (fun x:E=> peel (steps M x 1)); let u:=saved k M.length G
  refine ⟨hf.smooth.const_smul _,by positivity,fun i hi=> ?_⟩
  cases i with
  | zero=> unfold normJ; rw [norm_iteratedFDeriv_zero]; simp_rw [steps_zero, peel,G.mat_one,sub_self,star_zero,show @array G 0=0 from rfl,show ((0,0):Pair G)=0 from rfl,smul_zero,norm_zero]; simpa only [pow_zero,mul_one] using hf.nonneg
  | succ i=>
    have hh:= (hf.smul e⁻¹).order _ hi
    unfold normJ; apply hh.trans
    let w:ℝ:= 2*M.length
    have hw:0 ≤ w:=by unfold w; positivity
    have ht:(2*e*M.length)^(i+1) ≤ e*w^(i+1):= by
      rw [show (2*e*M.length)=e*w by unfold w; ring, mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hw _)
      calc _ ≤ e^1 := pow_le_pow_of_le_one he h (by omega)
           _ = e:= pow_one _
    have hu:0≤u:=hf.nonneg
    rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr he)]
    rcases eq_or_lt_of_le he with he|he
    · subst e; rw [_root_.inv_zero,zero_mul,zero_mul]; exact mul_nonneg hu (pow_nonneg hw _)
    apply (mul_le_mul_of_nonneg_left ht (show 0≤e⁻¹*u by positivity)).trans
    change e⁻¹*u* _ ≤ u*w^(i+1); apply le_of_eq; field_simp

lemma walk (u : Config G c) (k:ℕ)(z:Slab G c k)(p:Edge (Site c)): (chug k u z) p=
    steps (D:=ℝ) (List.ofFn (fun i=>ContinuousLinearMap.toSpanSingleton ℝ (z i p))) 1 (u p):=by
  induction k generalizing u with
  | zero=> simp [chug,steps,List.ofFn_zero]
  | succ k h=>
    unfold chug; rw [h,List.ofFn_succ]
    unfold Fin.tail increment steps; simp [one_smul]

def march (A:Slab G c n) (p:Edge (Site c)) (i:Fin n) := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i).smulRight (A i p)
lemma stepJourney (A:Slab G c n) (p:Edge (Site c)) (v : Config G c)(x:Panels n) : journey v n A x p=
    steps (List.ofFn (march A p)) x 1*v p :=by
  unfold journey; rw [walk]
  let f i := x i • A i p
  let L:=List.ofFn f
  have he {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (g:E)(u:G.El)(X:List (E→L[ℝ] G.Color)) : steps X g u=(X.map (fun i=>G.lieExp (i g))).foldl (fun A v=> v*A) 1 *u:=by
    induction X using List.reverseRecOn with
    | nil=> simp [steps]
    | append_singleton l i h=>
      unfold steps at *; rw [List.foldl_append,List.map_append,List.foldl_append]; simp only [List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]; rw [h,mul_assoc]
  simp_rw [he,List.map_ofFn]; simp only [Function.comp_def,ContinuousLinearMap.toSpanSingleton_apply, one_smul, Pi.smul_apply, mul_one]; rfl

variable (V:Config G c)(A:Slab G c n) (ε:Edge (Site c)→ℝ)
    (he:∀ p,0≤ε p)(hε:∀ p,ε p ≤ 1)(hA:∀ i p,‖A i p‖ ≤ ε p)
include he hε hA
lemma follow (k:ℕ):
    let g(t : Panels n):= encoded ε V (journey V n A t)
    Brush k (saved k n G) (2*n) g 0 ∧ g 0=0 ∧ ∀ t p,ε p=0→ journey V n A t p=V p:=by
  intro g
  have hx i (p:Edge (Site c)): ‖march A p i‖ ≤ ε p:= by
    apply ContinuousLinearMap.opNorm_le_bound _ (he p); intro t
    change ‖t i • A i p‖≤_
    rw [norm_smul,mul_comm]; exact mul_le_mul (hA i p) (norm_le_pi_norm t i) (norm_nonneg _) (he _)
  have ht(t p) : g t p = (ε p)⁻¹ • peel (steps (List.ofFn (march A p)) t 1) := by unfold g encoded peel; rw [stepJourney,mul_inv_cancel_right]
  refine ⟨?_,?_,?_⟩
  · apply all (fun i=>?_)
    let f:= List.ofFn (march A i)
    have hlen:f.length=n:=List.length_ofFn ..
    have hs:= (scaled f (ε i) k (he _) (hε _) (by intro a ha; obtain ⟨p,rfl⟩:=List.mem_ofFn.mp ha; exact hx ..)).shimmy (Eventually.of_forall (fun a=>ht a i))
    rw [hlen] at hs; exact hs
  · ext1 p; rw [Pi.zero_apply,ht,steps_zero]; simp_rw [peel,G.mat_one,sub_self,star_zero,show @array G 0=0 from rfl,show ((0,0):Pair G)=0 from rfl,smul_zero]
  intro t p hp; rw [stepJourney]
  have hh i:march A p i=0:=norm_le_zero_iff.mp ((hx i p).trans hp.le)
  suffices h : steps (List.ofFn (march A p)) t 1= (1:G.El) by rw [h,one_mul]
  have he (l:List (Panels n→L[ℝ]G.Color)) (h:∀ i∈l,i=0): steps l t 1=(1:G.El):=by
    induction l with
    | nil=>rfl
    | cons i l ih=>
      change steps l t (_*_) = _; rw [h i (List.mem_cons_self ..)]; simp only [_root_.zero_apply, Gauge.mat_lieExp_zero,one_mul]; apply ih fun i hi=> h i (List.mem_cons_of_mem _ hi)
  exact he _ (by intro a ha; obtain ⟨i,hi⟩:= List.mem_ofFn.mp ha; exact hi ▸ hh i)
end YM.RG01.Kernel
