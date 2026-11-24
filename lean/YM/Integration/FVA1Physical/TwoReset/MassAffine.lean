import YM.Integration.FVA1Physical.TwoReset.AffineGap

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Lattice Wilson RG RG.Supply Gauge Input Org Precision Tree
open AllOrder AllOrder.Floe AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open AllOrder.Laplace AllOrder.Laplace.SigmaP Laurent Stationary Pace AllOrder.Ink AllOrder.Ink.Money
open Extra.Iteration Primitives.TwoWave Primitives.TwoWave.RealSlice Finset UVExt.Paths
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace ReadAffine
open Bid Extra.Iteration Jets PertExtension.Series PertExtension.Series.Radial
variable {G: Gauge}{n : Side}
variable {A B u σ:ℝ}
variable {P Q:Layout G} {T:Finset Age}{q b:Pace.Coin}
variable {i j k N:ℕ}
variable {M : ℕ → Atom G 2}
variable {p:Clip}{R:PathData G}
set_option quotPrecheck false
local notation "X" n:max => (Link G n)
local notation "F" x:max y:max z:max=> (factor x y z) -- not using

/-- Exact affine price at EVERY period (no wrap/non-injective averaging excuse here). -/
def pair (a:G.Color) (F':AllOrder.Ink.Money.Bills (Coarse G)) (n:Side) : ℝ:=
    let x (z:ℂ) := (arm G n 1).symm (melody a n z)
    Radial.jet (F' n) 2 (x 1) + Radial.jet (F' n) 2 (x Complex.I)

variable (a:G.Color) (ha:‖a‖=1)
variable {F' G' : AllOrder.Ink.Money.Bills (Coarse G)}

abbrev Rated (P:Ink.Money.Bills (Coarse G)) := ∀ n, ContDiffAt ℝ ω (P n) 0
lemma rated_sum {ι:Type*}{g:ι→Ink.Money.Bills (Coarse G)} (t:Finset ι)
    (ht: ∀ i∈t,Rated (g i)): Rated (∑ i∈t,g i):= by
  intro n
  rw [show (∑ i∈t,g i) n = fun x=> ∑ i∈t,g i n x by ext x; simp only [Finset.sum_apply]]
  exact ContDiffAt.sum fun i hi=> ht i hi n

lemma pair_smul (h:Rated F') (r:ℝ):pair a (r • F') n = r*pair a F' n:= by
  unfold pair; dsimp only; rw [Pi.smul_apply]
  have ht(x:X n): Radial.jet (r • F' n) 2 x=r*Radial.jet (F' n) 2 x:= by unfold Radial.jet; rw [iteratedFDeriv_const_smul_apply ((h n).of_le le_top),_root_.smul_apply]; change _ * (r * _) = _; ring
  rw [ht,ht,mul_add]

lemma pair_add (h:Rated F') (H:Rated G'):pair a (F'+G') n=pair a F' n+pair a G' n:= by
  unfold pair; dsimp only; rw [Pi.add_apply,jet_add (h n) (H n),jet_add (h n) (H n)]; abel
lemma pair_sum {ι:Type*}{g:ι→Ink.Money.Bills (Coarse G)} (t:Finset ι)
    (ht: ∀ i∈t,Rated (g i)):pair a (∑ i∈t,g i) n=∑ i∈t,pair a (g i) n:= by
  induction t using Finset.induction_on with
  | empty => simp only [sum_empty]; unfold pair; simp [jet]
  | insert i u hi ih =>
    have hx(k) (hk:k∈u):= ht k (mem_insert_of_mem hk)
    rw [sum_insert hi,sum_insert hi,pair_add a (ht _ (mem_insert_self ..)) (rated_sum u hx),ih hx]

variable (V:ℕ → Ink.Money.Bills (Coarse G))
local notation "FΣ" q:max V:max i:max => (∑ j∈range (i+1),(q) (i-j) • V j)
theorem rateq (q:Pace.Coin) (i:ℕ):Pace.factor q V i= FΣ q V i:=by
  funext n; rw [Finset.sum_apply,weigh_right]
  rfl
lemma pair_factor {q:Pace.Coin} (k n) (he:∀ i:ℕ,Rated (V i)) : pair a (Pace.factor q V k) n = ∑ i∈ range (k+1), q (k-i)*pair a (V i) n:= by
  rw [rateq V q k,pair_sum (g:=fun i=> q (k-i) • V i) a _ (fun i _ n=> (he i n).const_smul (q (k-i)))]
  simp_rw [pair_smul a (he _)]

abbrev Muted (a:G.Color) (F':Ink.Money.Bills (Coarse G)):Prop:= Rated F' ∧ ∃ C:ℝ, ∀ n:Side, 4≤n.val → |pair a F' n| ≤ C

include ha
lemma quiet_pair (hp:0<σ)(hm: StateE.Quoted M σ B): Muted a (fun n=> Radial.jet (Stationary.turnSeries (m:=n) M) 2) := by
  constructor
  · intro n; exact (Haiku.Project.maturity _ _).read.smooth.contDiffAt
  let Q:=Extra.Iteration.momentPrice 2 σ*B
  let d:=(64*(4*Real.pi)^2)^2
  refine ⟨d*Q+d*Q,fun n hn=>?_⟩
  let U (z:ℂ):=melody a n z
  let x(z:ℂ):=(arm G n 1).symm (U z)
  let f := Radial.jet (Stationary.turnSeries (m:=n) M) 2
  have hg : 0 ≤ Q:= mul_nonneg (momentPrice_pos 2 hp).le hm.pays
  have h (z:ℂ)(hz:‖z‖≤1): |Radial.jet f 2 (x z)| ≤ d*Q := by
     have hx : Radial.jet f 2=f:= by
       unfold f
       ext1 x
       change (↑(Nat.factorial 2):ℝ)⁻¹ *iteratedFDeriv ℝ 2 _ 0 (fun _=>x)=_
       rw [Haiku.Project.self _ ((turns_analytic M hp hm.pay).contDiffAt)]; rfl
     have ht:= (cochain_tone a ha hn z hz).2
     rw [hx]; apply (pencils (n:=n) hp hm (x z) (U z) ((arm G n 1).apply_symm_apply _)).trans
     refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
       (mul_nonneg (show (0:ℝ)≤16 by norm_num) (norm_nonneg _)) (mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤16 by norm_num)) 2) (Nat.cast_nonneg _)) hg).trans_eq ?_
     rw [YM.Lattice.site_card, Nat.cast_pow]; unfold UVExt.Paths.ripple d; field_simp [show (↑n.val:ℝ)≠0 from Nat.cast_ne_zero.mpr n.pos.ne']; ring
  exact (abs_add_le ..).trans (add_le_add (h 1 (by simp)) (h Complex.I (by simp)))

omit ha
lemma zero_pair {F':Ink.Money.Bills (Coarse G)} (h:Rated F')(hx:∀ n, Radial.jet (F' n) 2=0): Muted a F':= by
  refine ⟨h,0,fun n _=>?_⟩
  simp [pair,hx]
lemma mute_sum {ι:Type*}{G':ι→Ink.Money.Bills (Coarse G)} (u:Finset ι)
    (h:∀ i∈u,Muted a (G' i)): Muted a (∑ i∈u,G' i):= by
  choose f hf using fun i hi=> (h i hi).2
  refine ⟨rated_sum u (fun i hi=> (h i hi).1), ∑ i:u, f i.val i.prop,fun n hn=>?_⟩
  rw [pair_sum a _ (fun i hi=> (h i hi).1), ← Finset.sum_coe_sort u]
  exact (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun x hx=> hf _ x.prop n hn)

lemma mute_factor {q:Pace.Coin}{i:ℕ} (h:∀ l:ℕ, Muted a (V l)): Muted a (Pace.factor q V i) := by
  rw [rateq V q i]; apply mute_sum
  intro j _
  obtain ⟨hk,c,hc⟩:= h j
  refine ⟨fun n=> (hk n).const_smul (q (i-j)), |q (i-j)| *c,fun n hn=>?_⟩
  rw [pair_smul a hk, abs_mul]; exact mul_le_mul_of_nonneg_left (hc n hn) (abs_nonneg _)

include ha
variable (hP:∀ i∈T,∃ v r:ℝ, 0<v∧ StateE.Quoted (P i) v r)
set_option quotPrecheck false
include hP
lemma no_bass : Muted a (glory q P T i):=by
  rw [glory,Finset.sum_apply]
  apply mute_sum; intro j hj
  obtain ⟨s,f,hs,hf⟩:= hP j hj
  apply mute_factor (G:=G) a (Haiku.Coat.trade j.e (P j)); intro l
  have h : Rated (Haiku.Coat.trade j.e (P j) l) := fun n=> (Haiku.Coat.trade_r _ _ n j.pricey).read.smooth.contDiffAt
  by_cases ht:j.e ≤ l
  · by_cases hu:l-j.e+j.r = 2
    · rcases j with ⟨g,k,p⟩
      obtain rfl : k=0 := by simp only [Age.r,Age.e] at hu; omega
      rw [show Haiku.Coat.trade ({grade:=g,slots:=0, paid:=p}:Age).e _ l = fun n=> Radial.jet (turnSeries (m:=n) (P ⟨g,0,p⟩)) 2 from funext fun n=> by unfold Haiku.Coat.trade; rw [if_pos ht,hu]]
      exact quiet_pair (M:=P ⟨g,0,p⟩) a ha hs hf
    refine zero_pair a h (fun n=>funext fun x=>?_)
    unfold Haiku.Coat.trade; rw [if_pos ht]; unfold Radial.jet
    change _ *iteratedFDeriv ℝ 2 (Radial.jet _ (l-j.e+j.r)) 0 _ = 0
    rw [Haiku.Project.other _ hu]; simp
  apply zero_pair a h
  intro n; unfold Haiku.Coat.trade; rw [if_neg ht]; ext x; simp [Radial.jet]

omit hP ha
open Work.F03
variable {B₁:Bed}{η η':ℝ} (hs:Attached B₁ R) (ht:∀ n,Floor B₁ p n η η')
variable (he:∀ n,Sworn B₁ n G) (hR:R.Bounds p σ A u)
local notation "Y" => Pace.base p R

lemma spec {q:Pace.Coin} : pair a (factor q (Y) i) n=q i*pair a (Y 0) n:=by
  rw [pair_factor a (Y) i n (fun i n=> (Haiku.Project.maturity _ _).read.smooth.contDiffAt), Finset.sum_eq_single 0,Nat.sub_zero]
  intro i hi hi'
  unfold pair; dsimp only
  simp only [show Radial.jet (Pace.base p R i n) 2=0 from funext fun x=> by change (↑(Nat.factorial 2):ℝ)⁻¹*iteratedFDeriv ℝ 2 (Radial.jet _ (i+2)) 0 _=0; rw [Haiku.Project.other _ (by omega)]; simp]
  all_goals simp

include he ht hs ha hR
open UVExt.Paths
lemma tier (hn:4≤n.val): p.direct * (n.val:ℝ)^2 ≤ 2 * pair a (Pace.base p R 0) n := by
  let v:=melody a n 1; let w:= melody a n Complex.I
  have hh (x:Link G n) : 2* Radial.jet (Y 0 n) 2 x=gaugeFiscal B₁ (arm G n 1 x) (arm G n 1 x):= by
    rw [show Y 0 n = Radial.jet (Stationary.inputSeries p R (m:=n)) 2 from Aero.headTwo p R hR]
    let f:=Stationary.inputSeries p R (m:=n); have h:ContDiffAt ℝ ω f 0:= ((Stationary.stain_knit R p hR).analytic).contDiffAt
    change 2*((↑(Nat.factorial 2):ℝ)⁻¹*iteratedFDeriv ℝ 2 (Radial.jet f 2) 0 (fun _=>x)) = _
    rw [Haiku.Project.self f h,show (fun _ : Fin 2=>x)=![x,x] from funext (fun i=> by fin_cases i <;> rfl)]
    rw [(show iteratedFDeriv ℝ 2 f 0 ![x,x]=_ from (Stationary.low_columns hR hs (ht _) (he _)).2.2 x x)]
    rw [←mul_assoc]; norm_num [Nat.factorial]
  unfold pair; dsimp only; rw [mul_add,hh _,hh _,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]
  have hv (t : Dir G n) : ∑ x:Site n, p.direct*‖Exterior.dColor G n 1 t (x,Exterior.plaquette coda)‖^2 ≤ gaugeFiscal B₁ t t := by
      rw [metric_pair _ hR hs _ _ (ht n), Fintype.sum_prod_type]
      refine Finset.sum_le_sum fun z _=> ?_
      let v (x : PlaqAxes) := p.direct * ‖Exterior.dColor G n 1 t (z,Exterior.plaquette x)‖^2 + ‖ellLine R (z,x) t‖^2
      have hq : ∑ x,v x = _ := Finset.sum_congr rfl fun x _=>Eq.symm <| congr_arg₂ (·+·) (congr_arg _ (real_inner_self_eq_norm_sq ..)) (real_inner_self_eq_norm_sq (ellLine R (z,x) t))
      exact le_trans (le_add_of_nonneg_right (sq_nonneg _)) ((Finset.single_le_sum (f:=v) (fun x (_ : x∈Finset.univ)=>by unfold v; positivity [p.quadratic_pos.le]) (Finset.mem_univ coda)).trans_eq hq)
  calc
     _ = ∑ x:Site n,p.direct * (1/(n.val:ℝ)^2) := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul, YM.Lattice.site_card, Nat.cast_pow]; field_simp [show ((n.val:ℝ)≠0) from by exact_mod_cast n.property.ne']
     _ ≤ (∑ x:Site n, p.direct*‖Exterior.dColor G n 1 v (x,Exterior.plaquette coda)‖^2) + (∑ x:Site n, p.direct*‖Exterior.dColor G n 1 w (x,Exterior.plaquette coda)‖^2) := Finset.sum_le_sum (fun x _ => (mul_le_mul_of_nonneg_left (tone_bill a x ha hn) p.quadratic_pos.le).trans_eq (by rw [mul_add])) |>.trans_eq Finset.sum_add_distrib
     _ ≤ _ := add_le_add (hv _) (hv _)
end ReadAffine
end YM.Integration.FVA1Physical.TwoReset

namespace YM.Integration.FVA1Physical.TwoReset.ReadAffine
open Function Filter Lattice Wilson RG RG.Supply Gauge Input Org Precision Tree
open AllOrder AllOrder.Floe AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire
open AllOrder.Laplace AllOrder.Laplace.SigmaP Laurent Stationary Pace AllOrder.Ink AllOrder.Ink.Money
open Extra.Iteration Primitives.TwoWave Primitives.TwoWave.RealSlice Finset UVExt.Paths
open Bid Extra.Iteration Jets PertExtension.Series PertExtension.Series.Radial
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G: Gauge}{n : Side}
variable {A B u σ:ℝ}
variable {P Q:Layout G} {T:Finset Age}{q b:Pace.Coin}
variable {i j k N:ℕ}
variable {M : ℕ → Atom G 2}
variable {p:Clip}{R:PathData G}
local notation "J"=> (Pace.base p R)
local notation "U"=> (J)+ AllOrder.Haiku.Coat.clerk (fun _=>Precision.loop R) 0
local notation "W"=> Pace.factor q J i
local notation "K"=> glory q P T i
local notation "Y"=> Pace.factor b J i
local notation "𝒱"=> glory b Q T i
local notation "j0" q:max P:max => (Pace.grouping q P T p R)

-- Equality of subtracted convention: terms under Γ and added sea all vanish at 0.
private lemma jet_money {f:Link G n→ℝ}{j:ℕ} (hk:j ≠ 0): Radial.jet f j 0=0:= by
   have he:= Tensor.homogeneous (Tensor.coeff f j 0) (0:Link G n) (0:ℝ)
   rw [zero_smul,zero_pow hk,zero_smul] at he; exact he
lemma honor_zero (q b:Pace.Coin)(P Q:Layout G)(T:Finset Age)(p:Clip)(R:PathData G)(i:ℕ)(n:Side) :
    Pace.grouping q P T p R i n 0=Pace.grouping b Q T p R i n 0:=by
  let F:= Pace.base p R
  have hx (s:Pace.Scene G)(q:Pace.Coin)(hc:∀ j,s j n 0=0): Pace.factor q s i n 0=0:=by rw [weigh_right,Finset.sum_apply]; exact Finset.sum_eq_zero (fun j _=>show q (i-j)*s j n 0=0 by rw [hc,mul_zero])
  have hu (P:Layout G)(q:Pace.Coin): Pace.glory q P T i n 0=0:= by
    unfold Pace.glory; simp_rw [Finset.sum_apply]; refine Finset.sum_eq_zero (fun j _=> hx (Haiku.Coat.trade j.e (P j)) _ fun k=>?_); unfold Haiku.Coat.trade; split; exact jet_money (by unfold Age.r; omega); rfl
  have hv (q:Pace.Coin): Pace.factor q F i n 0=0:= hx _ q fun j=> jet_money (by omega)
  simp only [Pace.grouping,Pace.shiftB,Pi.add_apply,hu]; rw [hv,hv]

variable (g:G.Simple)
variable (hP:∀ i∈T, ∃ v r:ℝ, 0<v∧StateE.Quoted (P i) v r)
variable (hQ:∀ i∈T, ∃ v r:ℝ, 0<v∧StateE.Quoted (Q i) v r)
variable {B₁:Bed}{η η':ℝ} (hs:Attached B₁ R) (ht:∀ n,Floor B₁ p n η η')
variable (he:∀ n,Sworn B₁ n G) (hR:R.Bounds p σ A u)
include he ht hs hR g hP hQ
lemma chosen_money (hh: Pace.grouping q P T p R i= Pace.grouping b Q T p R i): q i=b i:= by
   classical
   let a:G.Color:= EuclideanSpace.basisFun G.ColorIndex ℝ (Classical.choice (Stationary.colorAvail G g))
   have ha:‖a‖=1:= (EuclideanSpace.basisFun G.ColorIndex ℝ).norm_eq_one _
   obtain ⟨hx,C,hC⟩:=no_bass (q:=q) (i:=i) a ha hP
   obtain ⟨hy,D,hD⟩:=no_bass (q:=b) (i:=i) a ha hQ
   have hv(q:Pace.Coin): Rated (Pace.factor q (Pace.base p R) i):= fun n=> (((Pace.base_pose (N:=i) p R hR g).proceed q).rank i le_rfl n).read.smooth.contDiffAt
   have hz(n:Side):pair a (W) n+pair a K n=pair a (Y) n+pair a (𝒱) n:= by
       have h₀ : W+K=Y+𝒱:= by
         have h': U i+W+K=U i+Y+𝒱:=hh
         rw [add_assoc,add_assoc] at h'; exact add_left_cancel h'
       rw [← pair_add a (hv q) hx,h₀,pair_add a (hv b) hy]
   have h (n:Side)(hn:4 ≤ n.val):|q i-b i| * p.direct*(n.val:ℝ)^2 ≤ 2*(C+D):= by
       have hl:= tier (n:=n) a ha hs ht he hR hn
       have hh: (q i-b i)*pair a ((Pace.base p R) 0) n= pair a (𝒱) n-pair a (K) n:= by
           specialize hz n; rw [spec a,spec a] at hz; linarith only [hz]
       rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left hl (abs_nonneg _)).trans
       rw [mul_left_comm, ← abs_of_nonneg (a:=pair a ((Pace.base p R) 0) n) (by have hp : 0 ≤ p.direct * (n.val:ℝ)^2:= mul_nonneg p.quadratic_pos.le (sq_nonneg _); linarith), ← abs_mul,hh,add_comm C]
       exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hD n hn) (hC n hn))) (by norm_num)
   by_contra hu
   let c:= |q i-b i| * p.direct
   let y (i:ℕ):Side:= ⟨i+4,by omega⟩
   have ha : 0<c := mul_pos (abs_pos.mpr (sub_ne_zero.mpr hu)) p.quadratic_pos
   have ht: Tendsto (fun i : ℕ => (↑(y i).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (show id ≤ fun i => i+4 from fun i=> Nat.le_add_right ..) tendsto_id)
   obtain ⟨z,hz⟩:= Tendsto.eventually_gt_atTop ((tendsto_pow_atTop (show 2≠0 by decide)).comp ht |>.const_mul_atTop ha) (2*(C+D)) |>.exists
   exact not_le.mpr hz (h _ (Nat.le_add_left 4 z))
end YM.Integration.FVA1Physical.TwoReset.ReadAffine
