import YM.X.Pulse.Road
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
section
variable (a:Fin m→ Labels.Label G d)(f : Fin m→ Labels.Label G d→ₗ[ℂ] poly (Jam n G))
abbrev products {V I T:Type*}[Fintype I][CommSemiring T][AddCommGroup V][Module ℂ V][Algebra ℂ T](f:I→ V→ₗ[ℂ] T): MultilinearMap ℂ (fun _:I=>V) T:= ((MultilinearMap.mkPiRing T I 1).restrictScalars ℂ).compLinearMap f
lemma stocks{V I T:Type*}[Fintype I][CommSemiring T][AddCommGroup V][Module ℂ V][Algebra ℂ T](f:I→ V→ₗ[ℂ] T)(p:I→V): products f p=∏ i,f i (p i) := by simp [products]
def chapters (b:Z):= (Hinge.shock sale ∘ₗ LinearMap.mulLeft ℂ b).compMultilinearMap (products f)
lemma chapter_val (b:Z) : chapters f b a = Hinge.shock sale (b * (∏ i:Fin m, f i (a i))):= by -- binder order
    rw [chapters, LinearMap.compMultilinearMap_apply, stocks]; rfl
section drift
variable {I V:Type*}[Fintype I][DecidableEq I][AddCommGroup V][Module ℂ V]
abbrev alma (V:Type*)[AddCommGroup V][Module ℂ V](n:ℕ) := MultilinearMap ℂ (fun _:Fin n=> V) ℂ
def ocean(P: MultilinearMap ℂ (fun _:I=>V) ℂ)(b: Module.End ℂ V)(i:I):= P.compLinearMap (Function.update (fun _:I=>LinearMap.id) i b)
def passV (d:Module.End ℂ V)(P: MultilinearMap ℂ (fun _:I=>V) ℂ) := ∑ i:I,ocean P d i
lemma ocean_view (p:I→V)(i:I)(b:Module.End ℂ V)(P: MultilinearMap ℂ (fun _:I=>V) ℂ): ocean P b i p=P (Function.update p i (b (p i))):=by rw [ocean,MultilinearMap.compLinearMap_apply]; apply congr_arg; funext t; by_cases hv:t=i<;>simp [hv]
lemma pass_view (p:I→V)(b:Module.End ℂ V)(P:MultilinearMap ℂ (fun _:I=>V) ℂ): passV b P p=∑ i:I,P (Function.update p i (b (p i))):= by simp only [passV,MultilinearMap.sum_apply,ocean_view]
lemma pass_linear (p:I→V)(c:ℂ)(b f:Module.End ℂ V)(P:MultilinearMap ℂ (fun _:I=>V) ℂ) : passV (c • b+f) P p=c • passV b P p+passV f P p:= by simp only [pass_view,LinearMap.add_apply,LinearMap.smul_apply, MultilinearMap.map_update_add,MultilinearMap.map_update_smul,Finset.sum_add_distrib,Finset.smul_sum]
end drift
lemma chapter_insert (g:L→ₗ[ℂ] Z)(i:Fin m): chapters (Function.update f i g) 1 a= Hinge.shock sale (g (a i) * ∏ j∈ Finset.univ.erase i,f j (a j)):=by rw [chapter_val,one_mul,← Finset.mul_prod_erase _ (fun j=> Function.update f i g j (a j)) (Finset.mem_univ i),Function.update_self]; apply congr_arg; apply congr_arg; exact Finset.prod_congr rfl fun j hj=> by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
end
section
variable (t:ℝ) (B:ℕ)(o:Side)
def sales (m:ℕ) (e:ℝ) (x:Site n): L→ₗ[ℂ] Z:= (hairAt x).toLinearMap ∘ₗ held S e⁻¹ d m
lemma symbols (i:(F.level d).Index)(x:Site n): sales S k t x ((F.level d).basis i) = hairAt x (mint t (useWord S i) k):= by rw [sales,LinearMap.comp_apply,held_name]; unfold mint; apply congr_arg (hairAt x); rw [zpow_neg,zpow_natCast,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; push_cast; rw [inv_pow]; rfl
def hours (b:poly (Jam n G))(d:ℕ): alma (Labels.Label G d) m:= chapters (fun i=> sales (d:=d) S 0 t (x i)) b
def first_b (d:ℕ): alma (Labels.Label G d) m:= (∑ i:Fin m,chapters (Function.update (fun i=> sales (d:=d) S 0 t (x i)) i (sales S 1 t (x i))) 1)- hours S x t (gas G n) d
variable (v:Fin m → (F.level d).Index)
local notation "W"=> useWord S ∘ v
set_option quotPrecheck false
local notation "F₀"=> (F.level d).basis ∘ v
lemma hours_basis (b:poly (Jam n G)) : hours S x t b d F₀= collector Finset.univ x (fun i=> mint t (W i) 0) b:= by
    rw [hours,chapter_val,costP]; unfold pack; simp_rw [Function.comp_apply,symbols]
lemma hrs_update (b:Labels.Label G d)(i:Fin m): hours S x t 1 d (Function.update F₀ i b)= collector (Finset.univ.erase i) x (fun i=> mint t (W i) 0) (sales S 0 t (x i) b):=by rw [hours,chapter_val,one_mul,costP,← Finset.mul_prod_erase _ (fun j=> sales (d:=d) S 0 t (x j) ((Function.update F₀ i b) j)) (Finset.mem_univ i),Function.update_self]; apply congr_arg; apply congr_arg; unfold pack;exact Finset.prod_congr rfl fun j hj=> by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]; exact symbols S _ _ _ -- S t 
end
end YM.PositionX.Pulse
