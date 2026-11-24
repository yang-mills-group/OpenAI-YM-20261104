import YM.OPE.Strobe.Twain

/-!
# Annular product sites with a bounded aspect ratio and reflected arrays.

Keep the same physical `loops` of the Strobe construction, increasing only the
geometry allowances on a fixed family of tests, no change of trajectory.
This permits arbitrary subsets to be recentered about any one of their positions.
Payment with the enlarged fees is done in Propagation.lean/Jobs.lean. Core
geometry proof adapted from the homogeneous YM/OPE/Strobe/Twain.lean.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsR2RG
open OPE OPE.Yarn OPE.Strobe
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol OPE.Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{C:Family G}{k z i j l m p N:ℕ}
variable {r:ℕ→ℕ}
set_option quotPrecheck false
local notation "V" => Site (C.side m p)
local notation "Z"=> royal C m p
open Yarn.SitePlan Next.Rank.Station
variable {n b E:ℕ}{x:I→Site (C.side k p)}(i₀:I)
local notation "y" => ((loops C k p) ∘ x)
local notation "U'" i => ((Z (i)).place (fun j=>(y j) (i)))
local notation "ℓ" => (C.S.a k*n/4)
/-- Bound maximal radial distance by a multiple of the lower noncoincidence radius. -/
structure Annular (C:Family G)(k p n E:ℕ)(x:I→Site (C.side k p))(i₀:I) : Prop where
    home: x i₀=0
    close i : separation (x i) 0 ≤ E*n
    apart i j:i≠j→ n ≤ separation (x i) (x j)
section
variable (he:Annular C k p n E x i₀)(hm:8*(2*(C.S.a k) *(E*n:ℝ))≤ C.S.a m)(hl:Barrow C r m b j)(hx:Fintype.card I ≤ b)
include he
lemma Annular.loops0 (i:ℕ) : (y i₀) i=0:= by unfold Function.comp; rw [he.home, loops_id]
lemma Annular.tops (i:I): C.S.a k* (separation (x i) 0:ℝ) ≤ ‖C.S.place (x i)‖ ∧ ‖C.S.place (x i)‖≤ 2*(C.S.a k)*(E*n:ℝ) := let h := normC C k p (x i); ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast he.close i) (mul_nonneg zero_le_two (C.S.a_pos k|>.le)))⟩
include hm hl
lemma screen0 (hi:j≤ i) (v u: V × I) (hv:v.1≠u.1): (C.path.levels.budget i).B^8 ≤ separation ((U' i) v) ((U' i) u):=by
    have hy:= woven_behind (j:=k) (k:=i) (hl.hbar.trans hi) (fun i=> (mul_le_mul_of_nonneg_left (Annular.tops i₀ he i|>.2) (by norm_num : (0:ℝ)≤8)).trans hm) ((hl.apron i hi).2.2 p (hl.hbar.trans hi)) v u hv; apply le_trans (le_of_eq ?_) hy; exact pow_mul _ 4 2
lemma corners (hi : j ≤ i)  {t:ℕ}(ht:t ≤ (C.path.levels.budget i).B^8)(hp:∀ v z,v≠z→ t ≤ separation ((y v) i) ((y z) i))(v u:V × I) (hv:v≠u) : t ≤ separation ((U' i) v) ((U' i) u):=by
    by_cases h:v.1=u.1; rw [show u=(v.1,u.2) from Prod.ext h.symm rfl]
    · change t≤ separation ((U' i) (v.1,v.2)) _; refine le_trans (hp v.2 u.2 (fun h'=>hv (Prod.ext h h'))) (le_of_eq (seps x (hl.hbar.trans hi) ..).symm)
    exact ht.trans (screen0 i₀ he hm hl hi _ _ h)
include hx
lemma Habitat (hi:j ≤ i) : Occupancy ((Z i).place (fun j=>((loops C k p) ∘ x) j i)) (r i) := by
    apply OPE.Loom.bucket (b:= (C.path.levels.budget i).B^4) (pow_pos (C.path.levels.budget i|>.B_pos) _) (hx.trans ((hl.apron i hi).2.1)); exact woven_behind (j:=k) (k:=i) (hl.hbar.trans hi) (fun i=> (mul_le_mul_of_nonneg_left (Annular.tops i₀ he i|>.2) (by norm_num : (0:ℝ)≤8)).trans hm) ((hl.apron i hi).2.2 p (hl.hbar.trans hi))
lemma covers_band (hp:0<n)(hj: j=arch 100 C ((C.S.a k)*n/4))(hN:j ≤ i): Band C ((loops C k p) ∘ x) r i N m:=by
    have hz:0<ℓ:= div_pos (mul_pos (C.S.a_pos k) (Nat.cast_pos.mpr hp)) (by norm_num);
    refine ⟨fun j _ _ a=>?_,fun a hi _=> Habitat i₀ he hm hl hx (hN.trans hi),?_⟩
    · rw [show (C.path.levels.clock.op j p).ratio=C.S.toDepth j.le_succ p from ratio_same ..]; exact sails_parent (x a) j.le_succ
    intro t hi _; intro X v q h; apply corners i₀ he hm hl (hN.trans hi.le) _ _ v q h
    · have hh := (hl.apron t (hN.trans hi.le)).1; exact hh.trans (pow_le_pow_right₀ (C.path.levels.budget t).B_pos (by decide:2 ≤ 8))
    intro v z he'; refine lower_pair _ _ ?_; have hx:= (before 100 hz (hj ▸ hN.trans_lt hi : arch 100 C ℓ < t)); have hq:=he.apart v z he'
    let X:=C.S.a k; have he:X* (n:ℝ) ≤ ‖C.S.place (x v-x z)‖:=le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hq :(n:ℝ)≤ (separation (x v) (x z):ℝ)) (C.S.a_pos _).le) (by rw [OPE.Loom.separation_alt]; exact (normC C k p _).1)
    change 4* OPE.Loom.threshold C 100 t≤ ‖C.S.place (x v-x z)‖; unfold X at he; linarith only [he,hx]
end
abbrev raid (C:Family G)(I:Type)[Fintype I](E j:ℕ) := radiusCost C (Mast.spaces I*E) j
lemma plumed (C:Family G)(u:Type)[Fintype u](j:ℕ) : Fintype.card u*(32*stride C 100 j+1) ≤ (C.path.levels.budget j).B*(Mast.PatrolFee C u j-1):=by
    let D:=(C.path.levels.budget j).B; have he:1 ≤ D:=(C.path.levels.budget j).B_pos; let n:=Fintype.card u; let q:=OPE.Loom.count C 50 j
    have hQ:OPE.Loom.count C 100 j ≤ 2*q:= by
       apply Nat.ceil_le.mpr; push_cast; let x:=C.path.levels.clock.hatBeta (j+1); have hp:=Nat.le_ceil ((50:ℝ)*Real.log x); change 100*Real.log x ≤ 2*↑(OPE.Loom.count C 50 j); unfold OPE.Loom.count; push_cast; linarith only [hp]
    change n*(32*(D*_+4)+1) ≤ D*(200*(n+1)*(q+10)-1)
    rw [Nat.mul_sub_left_distrib,mul_one]; have hx:=Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 32 (Nat.add_le_add_right (Nat.mul_le_mul_left D (Nat.add_le_add_right hQ 2)) 4)) 1)
    refine hx.trans (Nat.le_sub_of_add_le ?_); nlinarith only [he,Nat.zero_le (n*D*q),Nat.zero_le (D*q),Nat.le_mul_of_pos_right n he]
variable (he : Annular C k p n E x i₀) (hp : 0<n)(hv: (C.S.a k)*n/4 ≤ OPE.Loom.threshold C 100 0) (hj : j=arch 100 C ((C.S.a k)*n/4)) (hm:m ≤ j)
include he hp hv hj hm
lemma investments (hE:0<E) (q:V × I) : coverNumber (C.path.levels.budget j).B ({(U' j) (q.1,i₀),(U' j) q}:Support _) ≤ raid C I E j :=by
    letI : Nonempty I:= ⟨i₀⟩; let c:=raid C I E j; let d:=separation ((y q.2) j) 0; have hV: (C.S.a k)*n/4>0:=by have := C.S.a_pos k; positivity
    have hh : (d:ℝ) ≤ 32*E*stride C 100 j+1:=by
       have ht: OPE.Loom.threshold C 100 j ≥ (C.S.a k)*n/4:= hj.symm ▸ arch_fails 100 hV hv; have he' := upper_pair (k:=j) (x q.2) 0; rw [sub_zero,loops_id] at he'; have hx: 0<C.S.a j:= C.S.a_pos _
       have hα := (Annular.tops i₀ he q.2).2
       apply le_of_mul_le_mul_left _ hx; change C.S.a j*(d:ℝ) ≤ _ at he'; unfold OPE.Loom.threshold at ht
       linarith only [mul_le_mul_of_nonneg_left ht (show (0:ℝ)≤ E by positivity),hα,hx,he', (by positivity: 0 ≤ (E:ℝ)*stride C 100 j*C.S.a j)]
    have hh': d ≤ (32*stride C 100 j+1)*E := by rw [← Nat.cast_le (α:=ℝ)]; push_cast; linarith only [hh,show (1:ℝ)≤ E by exact_mod_cast hE]
    have hδ:separation ((U' j) (q.1,i₀)) ((U' j) q)=d:=by rw [separation_comm]; change separation ((U' j) (q.fst,q.snd)) _= _; have he':=seps x hm q.1 q.2 i₀; rw [he.home,loops_id] at he'; exact he'
    have hB : d ≤ (C.path.levels.budget j).B*(c-1):= by
       refine (hh'.trans (Nat.mul_le_mul_right E ((Nat.le_mul_of_pos_left _ Fintype.card_pos).trans (plumed C I j)))).trans ?_
       rw [Nat.mul_assoc]; refine Nat.mul_le_mul_left _ ?_
       rw [Nat.mul_comm _ E,Nat.mul_sub]; have : raid C I E j= E*Mast.PatrolFee C I j := by unfold raid Mast.PatrolFee radiusCost; ring
       unfold c; omega
    apply le_trans (OPE.Loom.assembled _ _ (hδ.le.trans hB)); have hc:0<c:=by unfold c raid radiusCost Mast.spaces; positivity
    exact le_of_eq (Nat.sub_add_cancel hc)
end YM.GapsR2RG
