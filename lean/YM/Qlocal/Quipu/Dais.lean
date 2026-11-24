import YM.Qlocal.Quipu.Tender
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
-- extend wall across both legs. χ preserves quiet.𝒮
variable (x:rule ι n)(o:α→Site n) (Z:R.Mode)
namespace Dais
open Tender Turbin Lasso
variable (w : Slip (Point (ι⊕α)))(P : Slip (Point α)) (z:Site n)
local notation "Q"=> Eluder.χ R x o
local notation "T"=> wall Q
abbrev chain (w:Slip (Point (ι⊕α))): Slip (Point α):= w.filterMap fun | ⟨_,.inl _⟩ => none | ⟨z,.inr v⟩ => some (z,v)
abbrev coin (w:Slip (Point (ι⊕α))): Slip (Point ι):= w.filterMap fun | ⟨_,.inr _⟩ => none | ⟨z,.inl v⟩ => some (z,v)
omit [Fintype α][Fintype ι][DecidableEq α] in
lemma leaves_length : w.length=(chain w).length+(coin w).length:=by induction w with | nil=>rfl | cons i w ih=> rcases i with ⟨z,h|h⟩ <;> simp [chain,coin,ih,add_right_comm,add_assoc] <;> omega
def effect (w:Slip (Point α))(o:α→ Site n)(z:Site n): Poly R:= (w.map (fun i=> viewed R o (stood z i))).prod
local notation "P₀"=> (effect (R:=R) P o z)
lemma throne : wall Q (invoice z w)=algebraMap ℝ (Poly R) (invoice z (coin w) x) * effect (chain w) o z:= by
 induction w with
 | nil=> change wall Q (fun _=>1)=algebraMap ℝ (Poly R) 1 * 1; rw [sky_c,map_one,one_mul]
 | cons q w ih=>
    let g (i : Λ) : E→ℝ:= ξ i; have h (i:Λ) : Plausible (fun x:rule (ι⊕α) n=>x i):= Plausible.line (ξ i).toLinearMap
    rw [invoice_cons, pours_m _ (h (stood z q)) ((Ink.Field.ticket z w).2.1.read), sky_x, ih]; rcases q with ⟨i,q|q⟩
    · let F:= coin w; let f:= (z+ wrap _ i,q); let a:= x f; change _ = algebraMap ℝ (Poly R) (a*invoice z F x) *_; rw [_root_.map_mul]; exact (mul_assoc ..).symm -- check orientation.Q
    exact mul_left_comm ..
abbrev names (P:Slip (Point α)) : List α:= P.map Prod.snd
def good (Z:R.Mode) (P:Slip (Point α)): Prop:= (names P).Nodup ∧ (names P).toFinset= Z.val
abbrev likes (P:Slip (Point α))(o:α→ Site n)(z:Site n): Prop:= ∀ i∈P,o i.2=z+wrap n i.1
local notation "L"=>likes P o z
lemma worth : (P₀).part Z= if good Z P ∧ likes P o z then 1 else 0 := by
 induction P generalizing Z with
 | nil=> simp only [likes, List.not_mem_nil, IsEmpty.forall_iff, implies_true, forall_const,and_true, effect, List.map_nil,List.prod_nil,Poly.one_part]; have hx: good Z [] ↔ Z=R.quiet:= ⟨fun h=>Subtype.ext h.2.symm,fun h=> h ▸ ⟨List.nodup_nil,rfl⟩⟩; simp only [hx]
 | cons i P ih=>
    let v:=i.2; let ξ:=z+wrap n i.1; let u:= effect (R:=R) P o z; change (viewed R o (ξ,i.2)*u).part Z= _; have ht: likes (i::P) o z ↔ o v=ξ ∧ likes P o z:= by simp only [likes,List.forall_mem_cons]; rfl
    have hh: good Z (i::P) ↔ v∈Z.val ∧ good (away Z i.2) P:= by
       let f:=names P; let t:= f.toFinset; change (List.Nodup (v :: f) ∧ _ )↔ _; have he:(away Z i.2).val=Z.val.erase v:= Finset.sdiff_singleton_eq_erase ..; unfold good; rw [he]; change (_ ∧ (v :: f).toFinset= _) ↔ _ ∧ f.Nodup ∧ f.toFinset=_; rw [List.nodup_cons, List.toFinset_cons]; have hx:v∈t↔ v∈f:= List.mem_toFinset
       constructor
       · rintro ⟨⟨H,hq⟩,hr⟩; rw [←hr]; exact ⟨mem_insert_self ..,hq,(Finset.erase_insert (mt hx.mp H)).symm⟩ -- `erase_insert` ?
       rintro ⟨hp,hv,hq⟩; replace hq : t= Z.val.erase v:=hq; rw [←hx]; refine ⟨⟨hq.symm ▸ notMem_erase _ _,hv⟩,?_⟩; rw [show f.toFinset=_ from hq,insert_erase hp]
    simp only [ht,hh]; rw [mul_comm _ u]; unfold viewed; split
    next h=> have hk : o v=ξ:= h.symm; rw [slide, ih]; by_cases hv: v∈Z.val; simp only [if_pos hv]; split_ifs <;> (first|rfl| tauto); rw [if_neg hv,if_neg (fun H=> hv H.1.1)]
    next h=>rw [mul_zero,Poly.part_nil,if_neg (fun H=> h H.2.1.symm)]
    -- four cases simpler split in by_cases replace scripted
-- price projection REAL beam
lemma termwise : crystal R Z o (invoice z w) x = if good Z (chain w) ∧ likes (chain w) o z then invoice z (coin w) x else 0:= by
 rw [crystal,throne,mul_comm, idle,worth]; split <;> simp
end Dais
end YM.Qlocal.Quipu.Eluder
