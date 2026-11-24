import YM.FormalOPE.RG10.Gazebo.Tower
import YM.FormalOPE.RG10.Horizon.Matrix
/-!
# Transport and re-position formal perturbative frames

The affine spaces of real filtration / H perturbations of the unit with no coefficient costs.
These algebraic identities require the genuine canonical (engineering filtered) frames used by
both solves. `parameter` uses EXP data (limits later). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{d k:ℕ}
local notation "J" d=> Deck F d
local notation "K" d=> Matrix (Deck F d) (Deck F d) fps
local notation "L" d=> Matrix (Deck F d) (Deck F d) ℝ
local notation "T"=>PertExtension.Physical.Profile.n
local notation "ℳ" d=> Mark (Deck F d) PertExtension.Physical.Profile.n

private lemma tenants_mul {A B:L d}(h:A∈tents F d)(he:B∈tents F d): A*B∈tents F d:= by
 obtain ⟨ha,hx⟩:= (pinned (F:=F) _).1 h; obtain ⟨hb,_⟩:= (pinned (F:=F) _).1 he
 have hs:= (votes _).1 ha; have ht:= (votes _).1 hb; refine ⟨(votes _).mpr ⟨(Cut.mul hs.1 ht.1),?_⟩,funext fun i=>?_⟩
 · intro s
   let S:=swing (F:=F) d s; change (A*B)*S=S*(A*B); have ha : A*S=S*A:= hs.2 s; have hb:B*S=S*B:= ht.2 s; rw [mul_assoc,hb,← mul_assoc,ha,mul_assoc]
 change (A*B) (Deck.start F d) i=0; rw [Matrix.mul_apply]; refine sum_eq_zero fun j _=>mul_eq_zero_of_left (congr_fun hx j) _

local notation "ρ"=> Real
variable (A B : Matrix (Deck F d) (Deck F d) fps) (i:ℕ)
abbrev Stg (n:ℕ) : L d := of fun i j=> coeff n (A i j)
private lemma slice_add : Stg (A+B) i= Stg A i+Stg B i:= by ext i j; simp [Stg]
private lemma slice_sub : Stg (A-B) i= Stg A i-Stg B i:= by ext i j; simp [Stg]
private lemma slice_mul : Stg (A*B) i=∑ j∈antidiagonal i,(Stg A j.1)*(Stg B j.2):= by
 ext u v; simp only [Stg, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,map_sum,coeff_mul]; rw [sum_comm]

/-- all positive and constant increments in approved Lie variations at this horizon. -/
def Upright := ∀ i:ℕ, Stg (A-1) i∈ tents F d
namespace Upright
variable {A B}
lemma mul (ha:Upright A)(hb:Upright B) : Upright (A*B):= by
 intro i; rw [show A*B-1=((A-1)+(B-1))+(A-1)*(B-1) by noncomm_ring,slice_add,slice_add,slice_mul]; refine (tents F d).add_mem ((tents F d).add_mem (ha _) (hb _)) ?_
 -- Pi space vs Matrix def problem
 change ((∑ j∈antidiagonal i,(Stg (A-1) j.1 * Stg (B-1) j.2 : L d)) : FrameAt (Deck F d) ℝ) ∈ tents F d
 apply Submodule.sum_mem; intro _ _; exact tenants_mul (ha _) (hb _)
end Upright
section jump

/-- arbitrary reexpression (also if nonsimple, algebraic identities only) -/
structure Warp where
 x : fps
 atOrigin : constantCoeff x=0
namespace Warp
variable (p: Warp)

def charge : fps→ₐ[ℝ]fps:= PowerSeries.substAlgHom (Triangle.good p.x p.atOrigin)
lemma turning (φ:fps) : p.charge φ=subst p.x φ := by rw [charge,coe_substAlgHom]
lemma base (x:ℝ) : p.charge (C x)= C x:= by rw [turning,subst_C]; rfl
lemma smoothed (x : fps) : constantCoeff (p.charge x)=constantCoeff x := by rw [turning]; exact Triangle.substitutes_zero p.atOrigin
lemma worth (hA:Upright A) : Upright (A.map p.charge) := by
 intro i
 let y:= A-1; have he : A.map p.charge - 1 = y.map p.charge:= by ext i j : 1; by_cases hi:i=j<;>simp [y,hi]
 let e k:= coeff i (p.x^k)
 have ht : Stg (y.map p.charge) i=∑ j ∈ range (i+1), e j • Stg y j:= by
   ext k l; simp only [Stg, Matrix.of_apply,Matrix.map_apply,turning, AlignSeries.subst_finite p.atOrigin, Matrix.sum_apply,Matrix.smul_apply]; exact sum_congr rfl (fun _ _=> mul_comm ..)
 rw [he,ht]; apply Submodule.sum_mem; intro _ _; exact Submodule.smul_mem _ _ (hA _)
end Warp
end jump

lemma diag_one : (1:L d)= Physical.diag (Deck F d) := by ext i j; by_cases h:i=j <;> simp [h, Matrix.one_apply,Physical.diag]
lemma diag_at : Stg (1:K d) 0= Physical.diag (Deck F d) := by ext i j; by_cases h:i=j <;> simp [h, Matrix.one_apply,Stg, Physical.diag]
lemma zero_at (i:ℕ)(h:0 < i): Stg (1:K d) i=0:= by ext x y; by_cases H:x=y <;>simp [H,Stg, h.ne']
lemma Upright.obtainable (hw : Stg A 0-(1:L d) ∈ tents F d)(hk : ∀ i>0,Stg A i∈tents F d): Upright A:= by
 intro i; rw [slice_sub]; rcases Nat.eq_zero_or_pos i with h|h; subst i; rw [diag_at, ←diag_one]; exact hw
 rw [zero_at i h,sub_zero]; exact hk i h
lemma Upright.go {A:K d}(ha:Upright A) : Stg A 0-(1:L d) ∈ tents F d:= by have ht:= ha 0; rw [slice_sub,diag_at, ←diag_one] at ht; exact ht
lemma Upright.higher {A:K d}(ha:Upright A)(h:0 < i) : Stg A i∈ tents F d:= by have ht:=ha i; rw [slice_sub,zero_at i h,sub_zero] at ht; exact ht
end YM.FormalOPE.RG10.Carryon
