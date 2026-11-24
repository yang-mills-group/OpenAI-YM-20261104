import YM.OPE.Strobe.Helio
/-! Native scene pair geometry extended to arbitrary aspect-ratio bound.

For all measured tiles, cannot use `Strobe.Habits` for arbitrary shape families.
Keep the Aspect K (Lebesgue tests will only use shape windows with fixed bounds,
but arity/shape ANY finite bounds before the moment), enlarge passages and pay
back the late changes of groups. Adapted from Strobe/{Twain,Skein}.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pier.Scene
open OPE OPE.Strobe
open OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open OPE.Yarn.SitePlan Next.Rank.Station
local notation "B" i => (C.path.levels.budget (i)).B
local notation "s" i => C.S.a (i)
variable {n t b a wide:ℕ}{x:I→Site (C.side k p)}(i₀:I)
-- n=l shell parameter. single case arbitrary shell
local notation "y" => ((loops C k p) ∘ x)
local notation "U'" i => ((Z (i)).place (fun j=>(y j) (i)))
local notation "ℓ" => (C.S.a k*n/4)
structure Nearest (C:Family G)(k p n wide:ℕ)(x:I→Site (C.side k p))(i₀:I) : Prop where
    home: x i₀=0
    close i : separation (x i) 0 ≤ wide*n
    apart i j:i≠j→ n ≤ separation (x i) (x j)
-- convenient pad instance free layouts out to any limit. derive both frames.
section
variable (he:Nearest C k p n wide x i₀)(hm:8*(2*(C.S.a k) *((wide*n:ℕ):ℝ))≤ C.S.a m)(hl:Barrow C r m b j)(hx:Fintype.card I ≤ b) {f:ℝ}
include he
omit [Fintype I] [DecidableEq I] in
lemma Nearest.loops0 (i:ℕ) : (y i₀) i=0:= by unfold Function.comp; rw [he.home, loops_id]
omit [Fintype I] [DecidableEq I] in
lemma Nearest.tops (i:I): C.S.a k* (separation (x i) 0:ℝ) ≤ ‖C.S.place (x i)‖ ∧ ‖C.S.place (x i)‖≤ 2*(C.S.a k)*((wide*n:ℕ):ℝ) := let h := normC C k p (x i); ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast he.close i) (mul_nonneg zero_le_two (C.S.a_pos k|>.le)))⟩
include hm hl
lemma screen0Wide (hi:j≤ i) (v u: V × I) (hv:v.1≠u.1): (C.path.levels.budget i).B^8 ≤ separation ((U' i) v) ((U' i) u):=by
    have hy:= woven_behind (j:=k) (k:=i) (hl.hbar.trans hi) (fun i=> (mul_le_mul_of_nonneg_left (Nearest.tops i₀ he i|>.2) (by norm_num : (0:ℝ)≤8)).trans hm) ((hl.apron i hi).2.2 p (hl.hbar.trans hi)) v u hv; apply le_trans (le_of_eq ?_) hy; exact pow_mul _ 4 2
lemma cornersWide (hi : j ≤ i)  (ht:t ≤ (C.path.levels.budget i).B^8)(hp:∀ v z,v≠z→ t ≤ separation ((y v) i) ((y z) i))(v u:V × I) (hv:v≠u) : t ≤ separation ((U' i) v) ((U' i) u):=by
    by_cases h:v.1=u.1; rw [show u=(v.1,u.2) from Prod.ext h.symm rfl]; change t≤ separation ((U' i) (v.1,v.2)) _; refine le_trans (hp v.2 u.2 (fun h'=>hv (Prod.ext h h'))) (le_of_eq (seps x (hl.hbar.trans hi) ..).symm) -- syntax
    exact ht.trans (screen0Wide i₀ he hm hl hi _ _ h)
include hx
lemma HabitatWide (hi:j ≤ i) : Occupancy ((Z i).place (fun j=>((loops C k p) ∘ x) j i)) (r i) := by
    apply Loom.bucket (b:= (C.path.levels.budget i).B^4) (pow_pos (C.path.levels.budget i|>.B_pos) _) (hx.trans ((hl.apron i hi).2.1)); exact woven_behind (j:=k) (k:=i) (hl.hbar.trans hi) (fun i=> (mul_le_mul_of_nonneg_left (Nearest.tops i₀ he i|>.2) (by norm_num : (0:ℝ)≤8)).trans hm) ((hl.apron i hi).2.2 p (hl.hbar.trans hi))
lemma covers_bandWide (hp:0<n)(hj: j=arch 100 C ((C.S.a k)*n/4))(hN:j ≤ i): Band C ((loops C k p) ∘ x) r i N m:=by
    have hz:0<ℓ:= div_pos (mul_pos (C.S.a_pos k) (Nat.cast_pos.mpr hp)) (by norm_num);
    refine ⟨fun j _ _ a=>?_,fun a hi _=> HabitatWide i₀ he hm hl hx (hN.trans hi),?_⟩
    · rw [show (T|>.clock.op j p).ratio=C.S.toDepth j.le_succ p from ratio_same ..]; exact sails_parent (x a) j.le_succ
    intro t hi _ X v q h; apply cornersWide i₀ he hm hl (hN.trans hi.le) _ _ v q h
    · let B':=C.path.levels.budget t; have hh := (hl.apron t (hN.trans hi.le)).1; exact hh.trans (pow_le_pow_right₀ B'.B_pos (by decide:2 ≤ 8))
    intro v z he'; refine lower_pair _ _ ?_; have hx:= (before 100 hz (hj ▸ hN.trans_lt hi : arch 100 C ℓ < t)); have hq:=he.apart v z he'
    let X:=C.S.a k; have he:X* (n:ℝ) ≤ ‖C.S.place (x v-x z)‖:=le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hq :(n:ℝ)≤ (separation (x v) (x z):ℝ)) (C.S.a_pos _).le) (by rw [Loom.separation_alt]; exact (normC C k p _).1)
    change 4* threshold C 100 t≤ ‖C.S.place (x v-x z)‖; unfold X at he; linarith only [he,hx]
end
-- pay for event length
private lemma plumed (C:Family G)(u:Type)[Fintype u](j:ℕ) : Fintype.card u*(32*stride C 100 j+1) ≤ (C.path.levels.budget j).B*(Mast.PatrolFee C u j-1):=by
    let D:=(C.path.levels.budget j).B; have he:1 ≤ D:=(C.path.levels.budget j).B_pos; let n:=Fintype.card u; let q:= Loom.count C 50 j
    have hQ:Loom.count C 100 j ≤ 2*q:= by
       apply Nat.ceil_le.mpr; push_cast; let x:=C.path.levels.clock.hatBeta (j+1); have hp:=Nat.le_ceil ((50:ℝ)*Real.log x); change 100*Real.log x ≤ 2*↑(Loom.count C 50 j); unfold Loom.count; push_cast; linarith only [hp]
    change n*(32*(D*_+4)+1) ≤ D*(200*(n+1)*(q+10)-1)
    rw [Nat.mul_sub_left_distrib,mul_one]; have hx:=Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 32 (Nat.add_le_add_right (Nat.mul_le_mul_left D (Nat.add_le_add_right hQ 2)) 4)) 1)
    refine hx.trans (Nat.le_sub_of_add_le ?_); nlinarith only [he,Nat.zero_le (n*D*q),Nat.zero_le (D*q),Nat.le_mul_of_pos_right n he]
variable (he : Nearest C k p n wide x i₀) (hp : 0<n)(hv: (C.S.a k)*n/4 ≤ threshold C 100 0) (hj : j=arch 100 C ((C.S.a k)*n/4)) (hm:m ≤ j)
variable (hbig:1≤wide)
include he hp hv hj hm hbig
lemma investmentsWide (q:V × I) : coverNumber (C.path.levels.budget j).B ({(U' j) (q.1,i₀),(U' j) q}:Support _) ≤ Mast.PatrolFee C (Fin wide) j :=by
    letI : Nonempty I:= ⟨i₀⟩; let c:=Mast.PatrolFee C (Fin wide) j; let d:=separation ((y q.2) j) 0; have hV: (C.S.a k)*n/4>0:=by have := C.S.a_pos k; positivity
    have hh : d ≤ wide*(32*stride C 100 j+1):=by
       have ht: threshold C 100 j ≥ (C.S.a k)*n/4:= hj.symm ▸ arch_fails 100 hV hv; have he' := upper_pair (k:=j) (x q.2) 0; rw [sub_zero,loops_id] at he'; have hx: 0<C.S.a j:= C.S.a_pos _
       have hα := (Nearest.tops i₀ he q.2).2
       apply (Nat.cast_le (α:=ℝ)).mp; push_cast; unfold Loom.threshold at ht; apply le_of_mul_le_mul_left _ hx; change C.S.a j*(d:ℝ) ≤ _ at he'; 
       push_cast at hα
       have hh : C.S.a j ≤ (wide:ℝ)*C.S.a j :=
         le_mul_of_one_le_left hx.le (by exact_mod_cast hbig)
       nlinarith only [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α:=ℝ) wide),hα,hx,he',hh,
         mul_nonneg (Nat.cast_nonneg (α:=ℝ) wide) (mul_nonneg (Nat.cast_nonneg (stride C 100 j)) hx.le)]
    have hδ:separation ((U' j) (q.1,i₀)) ((U' j) q)=d:=by rw [separation_comm]; change separation ((U' j) (q.fst,q.snd)) _= _; have he':=seps x hm q.1 q.2 i₀; rw [he.home,loops_id] at he'; exact he'
    have hB : d ≤ (B j)*(c-1):= le_trans hh (by simpa only [Fintype.card_fin] using plumed C (Fin wide) j)
    apply le_trans (Loom.assembled _ _ (hδ.le.trans hB)); have hc:0<c:=Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.add_pos_right _ (by decide)); exact le_of_eq (Nat.sub_add_cancel hc)
end YM.Pier.Scene
