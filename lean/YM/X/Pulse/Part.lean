import YM.X.Pulse.Desk
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
variable (v:Fin m→(F.level d).Index)
local notation "U"=> Finset.univ
set_option quotPrecheck false
local notation "F₀"=> (F.level d).basis ∘ v
local notation "W"=> useWord S ∘ v
local notation "ε" => epsilon q k
lemma first_basis (e:ℝ): first_b S x e d F₀ = (∑ k:Fin m, collector (Finset.univ.erase k) x (fun i=> mint e (W i) 0) (hairAt (x k) (mint e (W k) 1))) -collector U x (fun i=> mint e (W i) 0) (gas G n):= by simp only [first_b,MultilinearMap.sub_apply,hours_basis,MultilinearMap.sum_apply,chapter_insert,costP,pack,Function.comp_apply,symbols]
abbrev partM (K:Bare.Shop F)(n:Side) (e:ℝ)(j:Fin m→ Site n)(d:ℕ)(b:ℕ): alma (E d) m:= (if b=0 then hours K j e 1 d else first_b K j e d).compLinearMap (fun _=> physicalLabel F d)
local notation "Ea"=>partM S
lemma coins_view (e:ℝ)(p:Fin m→ E d) : Ea n e x d 0 p=hours S x e 1 d (physicalLabel F d ∘ p):= rfl -- if decidable classical
lemma bill₁_view (e:ℝ)(p:Fin m→ E d) : Ea n e x d 1 p=first_b S x e d (physicalLabel F d ∘ p):= rfl
section rel
variable (s: Fin m→Site (side q k))
local notation "P₀"=>hours S s ε 1 d
local notation "P₁"=>first_b S s ε d
local notation "vB"=> physicalLabel F d ∘ₗ (Pulse.advance (q:=q) (k:=k) S w d)
lemma pass_wallet (i:Fin m): P₀ (Function.update F₀ i ((vB) (F₀ i)))= payer (Finset.univ.erase i) q k W s (hairAt (s i) (rebate q w k (W i) S)):= by
   rw [hrs_update]; apply congr_arg; unfold sales; rw [LinearMap.comp_apply, LinearMap.comp_apply, Function.comp_apply,advance_eq, helm];rfl
lemma first_subtract : P₁ F₀-passV vB P₀ F₀=due_bill q w Finset.univ W k s S:=by
    rw [first_basis,pass_view,due_bill]; have hg: collector U s (fun i=> mint ε (W i) 0) (gas G (side q k))=sphere_bill q U W k s:= by simp only [gas,Fintype.sum_prod_type,map_sum,sphere_bill]
    rw [hg]; simp_rw [pass_wallet,map_sub,Finset.sum_sub_distrib]; unfold payer; abel
lemma spend_reply (p:Fin m→ E d): passV (away (q:=q) (k:=k) S w d) (Ea _ ε s d 0) p= (passV vB P₀) (physicalLabel F d ∘ p):=by simp_rw [pass_view,coins_view S _,YM.PositionX.map_update];rfl
end rel
-- IO ∗any rank. For ∗all plots cost. output lift projection for χ fixed health. Γ preservation later.
lemma expand_basis {V I:Type*}[Fintype I][AddCommGroup V][Module ℂ V](p:Fin m→V)(B:Module.Basis I ℂ V)(a:ℕ→ alma V m)(X:Submodule ℂ (ℕ→ℂ))(h:∀q:Fin m→I,(fun k=> a k (B ∘ q))∈X): (fun k=> a k p) ∈ X:= by
   have ht(k):a k= Bare.spread B (fun q=> a k (B ∘ q)):= by apply Module.Basis.ext_multilinear (fun _=> B); intro v; exact (Bare.spread_eval B (fun q=> a k (B ∘ q)) v).symm
   have he(k):a k p= _:= congr_arg (fun F:alma V m=> F p) (ht k) |>.trans (Bare.spread_value ..) -- implicit
   rw [show (fun k=> a k p)=∑ q:Fin m→I,(∏ i:Fin m, B.coord (q i) (p i)) • (fun k=> a k (B ∘ q)) from ?_]; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (h i)
   ext1 k; rw [Finset.sum_apply, he] <;> rfl -- rfl clash
variable (y:Fin m → Fielding.Walk)(z:Fin m→E4)(hy:∀ i,plot q (y i) (z i)) {r:ℝ}(he:Porch.Apart U z r)(hr:R<r) (t:∀i:ℕ,Site (side q i))(hq:1<q.val)
def Clover (V:Type*)[AddCommGroup V][Module ℂ V] (q:ℕ+)(r:ℝ)(m:ℕ)(a:∀i:ℕ,(Fin m→Site (side q i))→ alma V m):Prop:= ∀ (y:Fin m → Fielding.Walk)(z:Fin m→E4),(∀i,plot q (y i) (z i))→ Porch.Apart U z r → ∀ (t:∀i:ℕ,Site (side q i)) (p:Fin m→ V), Released (fun i=> a i (postal y (t i) i) p)
-- for compensation Y. Expressed on Field d. X∗ frame no property
abbrev balance(q:ℕ+)(S:Shop F)(r:ℝ)(m:ℕ)(L₀:ℕ→ Module.End ℂ (E d)):= Clover (E d) q r m (fun i x=> partM S _ (epsilon q i) x d 1-passV (L₀ i) (partM S _ (epsilon q i) x d 0))
include hq hr
lemma light_res : balance q S r m (fun k=>away (q:=q) (k:=k) S w d):= by
    let H:= fun (k:ℕ)(z:Fin m→Site (side q k))=> first_b S z (epsilon q k) d -passV ((physicalLabel F d) ∘ₗ (advance (q:=q) (k:=k) S w d)) (hours S z (epsilon q k) 1 d);
    intro y z hy he u p; have ht(v:Fin m→ (F.level d).Index): (fun k=> H k (postal y (u k) k) ((F.level d).basis ∘ v))∈ Shelf.crew:= by change Released _; unfold H; simp only [MultilinearMap.sub_apply,first_subtract]; exact cost_bill q w U (useWord S ∘ v) y z (fun i _=>hy i) he hr u hq S
    simp_rw [MultilinearMap.sub_apply,bill₁_view S _,spend_reply]; exact expand_basis (physicalLabel F d ∘ p) (F.level d).basis (fun k=> H k (postal y (u k) k)) Shelf.crew ht
end YM.PositionX.Pulse
