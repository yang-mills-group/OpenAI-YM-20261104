import YM.X.Pulse.Peel
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
variable (Y:T→ℕ)
open Finset
variable {e:ℝ}(P:Fin k→Word G)
variable {j m:ℕ}(x:Fin m→ Site n)
local notation "Z"=> poly (Jam n G)
variable (e₀:ℝ)(Y₀:Fin m→ Word G)(v: Fin m → (F.level d).Index)
local notation "U"=> Finset.univ
set_option quotPrecheck false
local notation "Fo"=> (F.level d).basis ∘ v
local notation "W"=> useWord S ∘ v
section
abbrev bumpV (e:ℝ)(n:ℕ):ℂ:= Complex.ofReal (e^(4*n))
def countV :ℂ:= Complex.ofReal (∏ i:Fin m, e₀ ^ (-((Y₀ i).d:ℤ)))
lemma tolls_equal : Complex.ofReal (∏ i:Fin m,toll e₀ (Y₀ i))= bumpV e₀ m * countV e₀ Y₀:= by
    unfold toll countV; rw [bumpV,← Complex.ofReal_mul]; simp_rw [zpow_neg,zpow_natCast,div_eq_mul_inv, Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_mul]; -- edit
lemma aroundQ (z:poly (Jam n G))(b:Fin m→ℕ): chapters (fun i:Fin m=>sales S (b i) e₀ (x i)) (d:=d) z Fo=countV e₀ W* Hinge.shock sale (z*∏ i:Fin m,transfers x W (b i) i):= by
    rw [chapter_val]; let e:=e₀; let a(i:Fin m):=(↑(e ^ (-((W i).d:ℤ))):ℂ); let f(i:Fin m):=transfers x W (b i) i;
    have ht : ∏ i:Fin m,sales S (b i) e₀ (x i) (Fo i)= (countV e W) • ∏ i: Fin m, f i:= by
         simp_rw [Function.comp_apply,symbols,mint,RCLike.real_smul_eq_coe_smul (K:=ℂ), map_smul]; unfold countV; rw [Complex.ofReal_prod]; change (∏ i:Fin m,a i • f i)= (∏ i:Fin m,a i) • _; simp_rw [← C_mul',Finset.prod_mul_distrib]; rw [map_prod] -- order
    rw [ht,mul_smul_comm, map_smul];rfl
lemma open_panel : hours S x e₀ 1 d Fo=countV e₀ W * purePoint W x:= by rw [hours,aroundQ,purePoint,←point_prop0,one_mul];rfl
lemma bumpQ_pre : first_b S x e₀ d Fo= countV e₀ W * plusPoint W x:= by
    let f:=transfers x W 0; let g(k):=transfers x W 1 k; unfold plusPoint; rw [tune_b]; simp_rw [tune,MultilinearMap.sub_apply,MultilinearMap.sum_apply,aroundQ]; rw [mul_sub, ← Finset.mul_sum]; congr 1; -- level `_` may solve?
    · apply congr_arg; rw [← map_sum,← point_prop1,Stems.triangle, Jet.listed]; apply congr_arg; refine Finset.sum_congr rfl fun i _=>?_ ; rw [one_mul]; apply Finset.prod_congr rfl ; intro j _; by_cases hy:i=j<;> simp [hy,queue,Ne.symm]
    apply congr_arg; unfold fireline Hinge.fees gas; change Hinge.shock sale ((∑ p:Face (Per n),_) * road x W)= _; rw [Finset.sum_mul,map_sum,Fintype.sum_prod_type,Finset.sum_comm,point_prop0]; rfl -- fees live
include q
lemma native_m (v:ℕ): Charged q (fun k=>(bumpV (epsilon q k) v)⁻¹) := by
    simp_rw [bumpV,← Complex.ofReal_inv, ← zpow_natCast,← zpow_neg]; exact poised
lemma positive_cash (j k:ℕ):(bumpV (epsilon q k) j)≠0:= Complex.ofReal_ne_zero.mpr ((pow_pos (epsilon_pos ..) _).ne')
end
end YM.PositionX.Pulse
