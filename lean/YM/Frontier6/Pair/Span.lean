/- Adjusting the alignment interval in YM/MergeProof/North/Vert.lean. -/
import YM.MergeProof.North.Vert
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories Station Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge} {n:Side} (C:Family G) (J j m p k N d:ℕ)
set_option quotPrecheck false
local notation "H"=> C.path
local notation "Rb"=> C.path.levels.budget
local notation "P"=> hands C p J
local notation "V'"=> Site (C.side J p)
local notation "E"=> Mix.camp C p J
local notation "S"=> C.S
variable (a:Site (C.side j p))
local notation "o"=> bites C J j p a
local notation "v"=> loops C j p a
local notation "t"=> (Rb k).B
local notation "y"=> (C.S.place a)
local notation "W"=> fuga C.path.levels k
variable (hk:k≤j)
include hk
lemma longMaximizing {X:ℕ} (hp:W/16≤ ‖C.S.place a‖)(hh:‖C.S.place a‖ + C.S.a k ≤ C.S.a k * (X:ℕ)) :
    t^2+1 ≤ separation (v k) 0 ∧ separation (v k) 0 ≤ X:=by
    obtain ⟨h₁,h₂⟩:= normC C j p a
    let Z:= C.S.toDepth hk p; let B:= separation (v k) 0; let c:= Z.count.val
    have hV: 2*separation a (Z.embed (v k))< c:= (by rw [vote C _ _ _ _ hk]; exact midway _ (C.S.toDepth_odd hk p) _)
    have hz : separation (Z.embed (v k)) 0 = c*B:=by nth_rw 1 [show _= v k from rfl]; nth_rw 1 [show (0:Site (C.side j p))=Z.embed 0 from Z.root.map_zero.symm]; exact Station.both ..
    have hL:= separation_triangle a (Z.embed (v k)) 0; have hq:= separation_triangle (Z.embed (v k)) a 0; rw [separation_comm (Z.embed (v k)) a,hz] at hq; rw [hz] at hL
    have hy : C.S.a j*c=C.S.a k:= C.S.embeds_scale Z; have ha:= C.S.a_pos j; have hp':= C.S.a_pos k; have hb:1 ≤ ((t:ℕ):ℝ):=by exact_mod_cast (Rb k).B_pos
    constructor
    · have hs: C.S.a j*(separation a 0:ℝ) ≤ C.S.a k*(B+1:ℝ):=by
         rw [← hy]; refine (mul_le_mul_of_nonneg_left (show (separation a 0:ℝ)≤ ((c*B+c:ℕ):ℝ) from ?_) ha.le).trans_eq (by push_cast; ring)
         exact_mod_cast (show separation a 0 ≤ c*B+c by omega)
      have hv : (128*(t:ℝ)^2*C.S.a k)/16 ≤ 2*(C.S.a k*(B+1:ℝ)):= hp.trans (h₂.trans (le_trans (le_of_eq (mul_assoc ..)) (mul_le_mul_of_nonneg_left hs zero_le_two)))
      have ht:8*((t:ℕ):ℝ)^2 ≤ 2*((B:ℝ)+1):= by apply le_of_mul_le_mul_right (a:=C.S.a k) _ hp'; linarith only [hv]
      exact_mod_cast (show ((t:ℕ):ℝ)^2+1≤ (B:ℝ) from by nlinarith only [ht,hb])
    have hR: C.S.a k*B ≤ C.S.a k+‖y‖:= by
       rw [← hy,mul_assoc]; have hx: ((c*B:ℕ):ℝ)≤ c+(separation a 0:ℝ):= by exact_mod_cast (show c*B≤ c+separation a 0 by omega)
       rw [Nat.cast_mul] at hx; exact (mul_le_mul_of_nonneg_left hx ha.le).trans (by rw [mul_add]; linarith only [h₁])
    apply Nat.cast_le (α:=ℝ) |>.mp
    apply le_of_mul_le_mul_left _ hp'
    exact hR.trans (le_trans (le_of_eq (add_comm ..)) hh)

omit hk
def fusionSpan (A:Levels G) (i:ℕ) := 1+(A.S.block i).val*(512*(A.budget i).B^2)

lemma span_used (A:Levels G)(i:ℕ) : 4*fuga A i + A.S.a (i+1) ≤ A.S.a (i+1) * fusionSpan A i := by
    apply le_of_eq
    unfold fuga fusionSpan; push_cast
    have h : A.S.a i= A.S.a (i+1) * (A.S.block i).val := (A.S.embeds_scale (A.S.oneStep i 0)).symm
    rw [h]; ring
end
end YM.MergeProof.Ribbons
