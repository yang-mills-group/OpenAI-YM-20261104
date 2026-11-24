import YM.AllOrder.Quay.Boot
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Lattice Wilson RG Ovens Finset
open WilsonStartup WilsonStartup.Design WilsonStartup.Start WilsonStartup.Padded Floe Floe.Crest Till Tilt Burn
open PhysicalNext Repeat Pressure ConnectedActivityE6 ConnectedActivityE6.Coat Rosary
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {κ j k a c : ℕ}{σ ω' α T C:ℝ}
variable (p:BudgetPoint)(h:Clip)(β:ℝ)
-- Group exact sum oriented jobs
variable (k)
local notation "B"=>p.B
local notation "sM"=> offerS G p (tile h G) (Age.scope (k+2)) (gStep β)
local notation "w"=>Start.weight h β
variable (x:Site n)(U:Config G n)
abbrev costFace (c:ℝ) :ℝ:= (Fintype.card Signed:ℝ) *Fintype.card PlaqAxes*c
abbrev note (i:Key n) := errorW G k i.root ∘ i.frame
abbrev orbit (f:Key n → Config G n→ℝ) (x:Site n) := ∑ i:Signed,∑ j:PlaqAxes,f (batch x i j)
def pulpit (h:Clip)(β:ℝ)(G:Gauge)(k:ℕ)(n:Side)(z:Site n): Config G n→ ℝ:=orbit (fun i:Key n=> Start.weight h β • note (G:=G) k i) z -- G k order beware
lemma stageW (hk:4*(k+4)≤ p.B)(hb:0<β): sM n x U + pulpit h β G k n x U= w*orbit Key.accrual x U:= by
 rw [crown_juice k p h β x U hk hb] -- maybe p first order?
 unfold orbit pulpit note errorW Crest.short Key.accrual batch Key.frame Key.root Key.native; -- unfold orbit twice
 simp only [orbit,batch,WilsonStartup.residual, Finset.sum_apply,mul_sub_left_distrib, Pi.smul_apply, smul_eq_mul,Function.comp_apply,Finset.sum_sub_distrib]; simp_rw [← mul_sum]; ring
variable {f:Key n → Config G n→ℝ} (he:∀ (s:Signed)(b:Site n)(i:Key n),f (Key.perm s b i)=f i∘ pull s b)
include he
lemma mirrorW : PhysicalNext.Repeat.Trio.Mirrors (orbit f):=by
 intro x s b U; unfold orbit; simp only [Finset.sum_apply]; symm; rw [← (Equiv.mulLeft s).sum_comp]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun j _=> congr_fun (he s b (batch x i j)) U -- order x s maybe swapped
 simp
omit he
lemma note_oriented (s:Signed)(b:Site n)(i:Key n) : (note (G:=G) k (Key.perm s b i)) = note (G:=G) k i ∘ pull s b:= funext fun U=> congr_arg (errorW G k i.root) (Key.oriented i s b U)
lemma note_roam (n:Side): PhysicalNext.Repeat.Trio.Mirrors (pulpit h β G k n):= mirrorW (f:=fun i:Key n=>w • note (G:=G) k i) (fun s b i=> funext fun U=> congr_arg (w * ·) (congr_fun (note_oriented k s b i) U))
-- through all.Analytic.price emblem.
abbrev gold (G:Gauge) (k l P:ℕ):ℝ:= (errorW_price k G l P).choose
abbrev permit (G:Gauge) (k l P:ℕ):ℝ:= (errorW_price k G l P).choose_spec.choose
abbrev perCost (k:ℕ)(G:Gauge):= gold G k p.order p.power*p.threshold^(k+5)
lemma minted (G:Gauge)(k a b:ℕ): 0 < gold G k a b ∧ 0 < permit G k a b :=⟨(errorW_price k G a b).choose_spec.choose_spec.1, (errorW_price k G a b).choose_spec.choose_spec.2.1⟩
-- fairness sum.Approved from θ landscape.
lemma note_price (i:Key n) (hp:p.threshold ≤ permit G k p.order p.power)(hb:2≤p.B): Fairness p i.native (court i.native p.B) (note (G:=G) k i) (perCost p k G):= by
 rw [show note (G:=G) k i = errorW G k i.positive from funext fun U=> (errorW_send k i.root i.1 i.native U).symm]; refine Fairness.wider («X»:=touched i.positive) ?_ (i.skin_positive ▸ sits p i hb); refine ⟨errorW_regular k i.positive p, (errorW_price k G p.order p.power).choose_spec.choose_spec.2.2.2 _ rfl rfl hp n _ _ (i.skin_positive ▸ i.native_mem), errorW_one k i.positive, fun _ v=> errorW_hess k i.positive _ _⟩
lemma altar (hp:p.threshold≤ permit G k p.order p.power)(hb:2≤p.B): Fairness p x (court x p.B) (pulpit h β G k n x) (costFace (|w| *perCost p k G)):= by
 let q:=|w| *perCost p k G; have he:(∑ _ :Signed, ∑ _ :PlaqAxes, q)=costFace q:=by simp only [sum_const,card_univ,nsmul_eq_mul,costFace,mul_assoc]
 unfold pulpit orbit; rw [←he]; exact Fairness.enroll univ fun i _=> Fairness.enroll univ fun j _=> (note_price k p (batch x i j) hp hb).scale w
end YM.AllOrder.Quay
