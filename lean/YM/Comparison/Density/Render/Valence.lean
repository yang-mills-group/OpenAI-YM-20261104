import YM.Comparison.Density.Render.Docks

/-!
Slot/color polynomial real ordinary Lie estimates. No Frobenius-dim
cost changing with period. Every path length, no truncation at diameter
or minimum torus path. Also certify valuation by actual derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Render
open Fusing Markers RG Lattice Function Finset MeasureTheory Filter Wilson
open Ovens Extra.Iteration
open Progress.DirectedRecipe AnalyticBridge.VerifiedReset AnalyticBridge.VerifiedReset.Collection
open WilsonStartup Averaging Geo Next.Scheduling Next.Scheduling.Wages Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff InnerProductSpace
open Transport AnalyticBridge.SectorAffine.Offset FreeResolvent.Affine FreeResolvent.TestD
variable {G : Gauge} {n : Side} {k t m : ℕ}
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

abbrev bil := ContinuousLinearMap.mul ℝ ℝ
def couple (k : ℕ) := 2^k * ‖bil‖ -- lean instances
lemma code_nn (k : ℕ) : 0 ≤ couple k:= by unfold couple bil; positivity
lemma seam (x : X) {f g : X→ℝ} {a b : ℝ} (hf : Through m f x a) (hg : Through m g x b): Through m (fun y=> f y*g y) x (couple m*a*b):= by
  exact (stitch bil hf hg).mono (by unfold couple; apply le_of_eq; ring)
lemma band {x : X} {ι : Type*} {f : ι→X→ℝ} {a : ℝ} {s : Finset ι} (hf : ∀ i∈s, Through k (f i) x a):
    Through k (fun u=>∏ i∈s,f i u) x ((couple k*a)^s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty=>
    simp only [prod_empty, card_empty,pow_zero]
    refine ⟨contDiffAt_const, fun i _=>?_⟩; by_cases h:i=0
    · subst i; rw [norm_iteratedFDeriv_zero]; simp
    rw [iteratedFDeriv_const_of_ne h]; simp
  | @insert i s he ih=>
    simp_rw [prod_insert he,card_insert_of_notMem he,pow_succ']
    exact seam x (hf _ (mem_insert_self ..)) (ih (fun _ hi=> hf _ (mem_insert_of_mem hi)))

private lemma detour_size (s : RG.Slot) : (Wages.detour s).length ≤ 2*s.length := by
  simp only [Wages.detour,Lattice.reverse,List.length_reverse,List.length_map,List.length_append, RG.Slot.length, square,List.length_cons,List.length_nil]; omega

def pass (G : Gauge) (k : ℕ) := G.colorScale⁻¹*ticket G (meter G k) k*2^k
lemma tick_nn (G : Gauge) (k : ℕ) : 0≤ticket G (meter G k) k:= by have := meter_nn G k; unfold ticket; positivity
lemma pass_nn (G : Gauge) (k : ℕ) : 0 ≤ pass G k:= by unfold pass; have := tick_nn G k; have := G.colorScale_pos; positivity

def roll (s : RG.Slot) (U : Config G n) (x : Site n) := travel U x (Wages.detour s)
lemma transported (s : RG.Slot) (U : Config G n) (x : Site n) : s.atSite U x=G.curvature (roll s U x):= by
  rw [Wages.hangs,← Wages.Path.picture]; rfl

lemma slot_test (s : RG.Slot) {V : Directions G n} (hv : ‖V‖≤1) (o : Site n) (l : ℕ) (hx : s.length≤l) :
    Through k (fun y : Directions G n=> s.atSite (increment 1 y) o) V (pass G k * (1+(l:ℝ))^k) := by
  simp_rw [Wages.hangs,← Wages.Path.picture]
  have hW:= worded (k:=k) o (Wages.detour s) hv
  refine (abroad hW (Wages.projector G)).mono ?_
  have h := ContinuousLinearMap.opNorm_le_bound (Wages.projector G) (inv_nonneg.mpr G.colorScale_pos.le) (Wages.norm_projector G)
  have hQ : ((detour s).length:ℝ) ≤ 2*(l:ℝ):= by exact_mod_cast (detour_size s).trans (Nat.mul_le_mul_left 2 hx)
  unfold pass; calc _ ≤ G.colorScale⁻¹*(ticket G (meter G k) k * (2*(1+(l:ℝ)))^k) := mul_le_mul h (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hQ]) k) (tick_nn ..)) hW.nonneg (inv_nonneg.mpr G.colorScale_pos.le)
                    _ = _ := by rw [mul_pow]; ring

lemma oneColor (i : G.ColorIndex) {x : X} {f : X→ G.Color} {a : ℝ} (h : Through k f x a) : Through k (fun y=> f y i) x a:= by
  let L : G.Color →L[ℝ]ℝ := EuclideanSpace.proj i
  have hp : ‖L‖≤ 1:= ContinuousLinearMap.opNorm_le_bound L zero_le_one fun u=> by
    change |u i| ≤ 1*_
    rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ u i]; exact (abs_real_inner_le_norm ..).trans (by rw [OrthonormalBasis.norm_eq_one])
  exact (abroad h L).mono (mul_le_of_le_one_left h.nonneg hp)
lemma bundle (a : Atom G t) (x : X) (f : Fin t → X→G.Color) {c : ℝ} (h : ∀ i,Through k (f i) x c) :
    Through k (fun y=>a.poly fun i=> f i y) x (a.magnitude * (couple k*c)^t) := by
  let F j u:= a.coeff j*∏ i,(f i u (j i))
  let K j:= |a.coeff j| *(couple k*c)^t
  have he (j): Through k (F j) x (K j):= by
    have hq:= band (s:=univ) (fun i (_:_∈ univ)=> oneColor (j i) (h i))
    rw [card_univ,Fintype.card_fin] at hq; exact hq.scale (a.coeff j)
  have hb := through_sum univ K F k x (fun i _=> he i)
  rw [show (∑ i,K i)=_ from (show (∑ i,K i)=a.magnitude*(couple k*c)^t by unfold Atom.magnitude; rw [sum_mul]) ] at hb
  rw [show (fun y=> a.poly fun i=>f i y)=∑ i,F i from funext fun y=> by rw [Finset.sum_apply]; rfl]; exact hb

def entry (G : Gauge) (t k : ℕ):= (couple k*pass G k)^t
def fareAt (a : RG.Atom G t) (k : ℕ) := a.magnitude*entry G t k * (1+(a.length:ℝ))^(k*t)
lemma reserved (a : Atom G t) (o : Site n) {x : Directions G n} (hx : ‖x‖≤1) : Through k (fun y=>a.unmasked (increment 1 y) o) x (fareAt a k) := by
  have h i : Through k _ x _:= slot_test (a.leg i) hx o a.length (Finset.single_le_sum (f:=fun i => (a.leg i).length) (fun _ _=>Nat.zero_le _) (mem_univ i))
  have he:= bundle a x _ h
  unfold fareAt entry; rw [pow_mul,mul_assoc a.magnitude,← mul_pow,mul_assoc]
  exact he

lemma vanish_prod (x : X) {ι:Type} (s : Finset ι) (f : ι→ X →ℝ) (h : ∀ i, f i x=0) (hf : ∀ i,ContDiffAt ℝ k (f i) x)
    (v : Fin t→ X) (l : List (Fin t)) (he : l.length<s.card) (hh : l.length≤ k):
    jet v (fun y=>∏ i∈s,f i y) l x=0:= by
  classical
  induction s using Finset.induction_on generalizing l with
  | empty=> simp at he
  | @insert i s htZ ih=>
    have ht : ContDiffAt ℝ k (fun y=>∏ i∈s,f i y) x:=contDiffAt_prod (fun i _=> hf i)
    simp_rw [prod_insert htZ]
    refine (leibniz v bil l (smooth_of_le (hf i) hh) (smooth_of_le ht hh)).trans ?_
    refine sum_eq_zero fun i' _=>?_
    by_cases hq : lo l i'=[]
    · rw [hq, zeroth v, h i,map_zero]; rfl
    have hz:= lengths l i'; have hj:= List.length_pos_iff.mpr hq; rw [card_insert_of_notMem htZ] at he
    rw [ih (hi l i') (by omega) (by omega),map_zero]

lemma valuation (a : Atom G t) (j : ℕ) (hj : j<t) (o : Site n):
    iteratedFDeriv ℝ j (fun y : Directions G n=> a.unmasked (increment 1 y) o) 0=0:= by
  refine norm_le_zero_iff.mp (list_op le_rfl (fun l v hl he=>?_))
  let X (i: Fin t) (y:Directions G n):= (a.leg i).atSite (increment 1 y) o
  have hX i z : Through j (fun y:Directions G n=> X i y z) 0 _:= oneColor z (slot_test (a.leg i) (norm_zero.le.trans zero_le_one) o (a.leg i).length le_rfl)
  have ha i : X i 0=0 := by dsimp [X]; rw [Work.G07.at_zero_increment,transported]; simp [roll,unitTravel,G.curvature_unit]
  let u (b:Fin t →G.ColorIndex) (y : Directions G n):= ∏ i, X i y (b i)
  have hP b : ContDiffAt ℝ j (u b) 0:=contDiffAt_prod (fun i _=> (hX i _).smooth)
  let U:= fun y=> ∑ b,a.coeff b*u b y
  change ‖jet v U l 0‖ ≤ 0
  unfold U
  rw [FreeResolvent.TestD.jet_sum v l univ (fun b y=> a.coeff b*u b y) (fun b hb=> (smooth_of_le (A:=fun y=> a.coeff b*u b y) (contDiffAt_const.mul (hP b)) hl.le))]
  rw [sum_eq_zero fun b _=> ?_,norm_zero]; change jet v (fun y=> a.coeff b • u b y) l 0=0
  let L:ℝ→L[ℝ]ℝ:= a.coeff b • ContinuousLinearMap.id ℝ ℝ
  rw [show jet v (fun y=> a.coeff b • u b y) l 0=L (jet v (u b) l 0) from jet_linear _ _ L (smooth_of_le (hP b) hl.le)]
  rw [show jet v (u b) l 0 = 0 from vanish_prod _ univ _ (fun i=> by simp only [ha]; rfl) (fun i=> (hX i (b i)).smooth) v l (by simpa [hl]) hl.le,map_zero]
end YM.Comparison.Density.Render
