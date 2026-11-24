import YM.X.Journey.Beam
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
variable (e₀:ℝ)(v:Fin m→ (F.level d).Index) (L₀:ℕ→ Module.End ℂ (Pert.Position.E F d))
set_option quotPrecheck false
local notation "W"=>useWord S ∘ v
local notation "F₀"=>(F.level d).basis ∘ v
local notation "ep" r=> bumpV r m
local notation "U"=> Finset.univ
def spirit (x: Fin m→Site n)(r:ℝ)(f:Fin m→ Word G)(j:ℕ):ℂ:= (bumpV r m)⁻¹ * Complex.ofReal (rowP x f r j)
def outerV (K:Bare.Shop F)(e:ℝ)(x:Fin m→ Site n)(d j:ℕ): alma (Labels.Label G d) m:= offspring F K.H K.S K.hS K.hP d (fun f=>spirit x e f j)
lemma outer_basis (j:ℕ): outerV S e₀ x d j F₀= spirit x e₀ W j := Bare.spread_eval ..
def outerK (K:Bare.Shop F)(r:ℝ)(x:Fin m→ Site n)(d j:ℕ): alma (Pert.Position.E F d) m:= (outerV K r x d j).compLinearMap (fun _=> physicalLabel F d)
variable [AddCommGroup V][Module ℂ V]
variable (a:Fin m→Beam q)(o:Beam q)(hw:Away o (-o))(hx:∀ i,Near o (a i))(hq:1<q.val)(hg:G.Simple)
local notation "Fℕ"=>(atTop:Filter ℕ)
include q in
lemma payday (h e:ℕ→ℂ)(f:ℕ→ℂ)(n:ℕ)(hp : Vanished q (fun k=> h k-bumpV (epsilon q k) n * f k)) (he:e=(fun k=> (bumpV (epsilon q k) n)⁻¹ * h k)) : Vanished q (e-f):= by
    rw [he, show ((fun k=> _) - f) = (fun k=> (bumpV (epsilon q k) n)⁻¹ )*(fun k=> h k-bumpV (epsilon q k) n*f k) from ?_]; exact Vanished.right (native_m _) hp
    ext1 i; simp only [Pi.sub_apply,Pi.mul_apply,mul_sub,←mul_assoc, inv_mul_cancel₀ (positive_cash n i),one_mul]
def vase(q:ℕ+): Submodule ℂ (ℕ→ℂ) where
    carrier:= {x| Vanished q x}; add_mem' {p z} h hx:= Vanished.add h hx; zero_mem':= Vanished.zero; smul_mem' d x h:= Vanished.right (Charged.constant d) h
include hw hx hq
lemma approach_zero (x:Fin m→ E d): Vanished q (fun k=> (outerK S (epsilon q k) (fun i=> a i k) d 0 -partM S (side q k) (epsilon q k) (fun i=>a i k) d 0) x) := by
    apply expand_basis (physicalLabel F d ∘ x) (F.level d).basis (fun k=> outerV S (epsilon q k) (fun i=>a i k) d 0-hours S (fun i=>a i k) (epsilon q k) 1 d) (vase q); intro v; change Vanished q _; simp_rw [MultilinearMap.sub_apply,open_panel, outer_basis,spirit]; apply payday _ _ _ m (fun d=>?_) rfl
    refine (cut_basis0 hq a o hw hx (useWord S ∘ v) d).congr_left ?_ -- provide W hygiene
    intro k; rw [tolls_equal,mul_assoc]
include hg
lemma approach_plus (x:Fin m→ E d): Vanished q (fun k=> (outerK S (epsilon q k) (fun i=> a i k) d 1 -partM S (side q k) (epsilon q k) (fun i=>a i k) d 1) x) := by
    apply expand_basis (physicalLabel F d ∘ x) (F.level d).basis (fun k=> outerV S (epsilon q k) (fun i=>a i k) d 1-first_b S (fun i=>a i k) (epsilon q k) d) (vase q); intro v; change Vanished q _; simp_rw [MultilinearMap.sub_apply,bumpQ_pre, outer_basis,spirit]; apply payday _ _ _ m (fun d=>?_) rfl; refine (cut_basis1 hq a o hw hx (useWord S ∘ v) hg d).congr_left ?_; intro k; rw [tolls_equal,mul_assoc]
omit hw hx hq hg
lemma growth(cost:ℕ→alma V m)(h:∀ x:Fin m→V,Vanished q (fun k=> cost k x))(f:ℕ→V)(he:f∈ Trust q V)(i:Fin m)(p:Fin m→V): Vanished q (fun k=> cost k (Function.update p i (f k))):=by
    induction he using Submodule.span_induction with
    | mem _ hp=> obtain ⟨c,v,hc,_,rfl⟩:=hp;simp_rw [MultilinearMap.map_update_smul];exact Vanished.right hc (h _)
    | zero=> simp_rw [Pi.zero_apply,MultilinearMap.map_update_zero];exact Vanished.zero
    | add x y _ _ a b=> simp_rw [Pi.add_apply,MultilinearMap.map_update_add]; exact a.add b
    | smul t y _ a=> simp_rw [Pi.smul_apply,MultilinearMap.map_update_smul]; exact Vanished.right (Charged.constant t) a
local notation "u" k=> fun i=> a i k
local notation "G₁" k:arg j=> outerK S (epsilon q k) (fun i=> a i k) d j
local notation "M₁" k:arg j=> partM S (side q k) (epsilon q k) (fun i=> a i k) d j
include hw hx hq hg
lemma courtesy (H:∀ v:E d,(fun k=> L₀ k v)∈ Trust q (Pert.Position.E F d))(x: Fin m→ E d): Vanished q (fun k=> ((G₁ k 1)-passV (L₀ k) (G₁ k 0)) x- ((M₁ k 1)-passV (L₀ k) (M₁ k 0)) x):= by
    have hc:= approach_plus S a o hw hx hq hg x; let f(i:Fin m):= fun k=>  ((G₁ k 0)-(M₁ k 0)) (Function.update x i (L₀ k (x i))); -- edit bracket
    have he:Vanished q (fun k=> passV (L₀ k) (G₁ k 0) x -passV (L₀ k) (M₁ k 0) x):= by simp_rw [pass_view, ←Finset.sum_sub_distrib]; refine ((show (fun k=> _)=∑ i:Fin m,f i from ?_ ) ▸ Vanished.finSum (fun i _=> growth _ (approach_zero S a o hw hx hq) _ (H (x i)) i x)); ext1 k;rw [Finset.sum_apply]; rfl
    simp only [MultilinearMap.sub_apply]; refine Eq.mp (congr_arg (Vanished (V:=ℂ) q) ?_) (hc.sub he); -- syntax
    ext1 k; change (((G₁ k 1) x-(M₁ k 1) x)-(_-_))=_; abel

end YM.PositionX.Pulse
