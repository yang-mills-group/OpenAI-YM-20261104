import YM.RG17.Press
import YM.FullVolume.Fields.Peat
/-!
# Commit `PRESS` readouts to exact origins, producing actual Serves
 Geometry REQUIRED: migrate slots aligned in every actual Step. E.g. use
 an adapted centered-grid sub-probe (prove sampling and readiness separately
 AT need), not charge for every term of arbitrary `bank` at N by this premise.
 Price extraction from real Services; wounds full Poly identities verified.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Finset Function Filter MeasureTheory Lattice RG Pressure Wilson Marker Source Overlay Extra.Histories
open FullVolume.Sever MergeProof MergeProof.Accent Motion Extra.Trajectories Extra.Multi Next.Rank Edition Spindle
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
variable {n:ℕ}{Γ:Census (Fin n)}{G:Gauge} {C:Family G} {N k p:ℕ}
    {S:Table C.book}{f:Extraction.Order}(W:OPE.Services C f S) (hc:C.Makes)
variable {w:Fin n→ℝ}
variable (s:Fin n → C.book.Token)(o:(j:ℕ)→Fin n→Site (C.side j p))
local notation "A"=> C.path
local notation "ρ"=> C.path.rep N p
local notation "µ"=> prior G
local notation "δ"=> fun i=> (s i).1
local notation "ε"=>fun i=> (s i).2

-- exact polynomial values used by root bills, full caliper.
def packStorm (s:Fin n→ C.book.Token) (x: Fin n → Site (C.side N p))(j:ℕ)(U:Config G (C.side j p)) : Poly Γ := Poly.inject (fun i=>pullDimes s x i j U)
local notation "X"=> packStorm (Γ:=Γ) (C:=C) s (p:=p) (N:=N) (o N)
local notation "g"=> (fun _ : Fin n=> ((1,false):Motion))
def skySeeds (N:ℕ)(i:Fin n):=MergeProof.item C (s i).1 N p (s i).2 (fun j=>o j i) (1,false) -- fix
local notation "Z"=> skySeeds s o N
local notation "T"=> Accent.birth Γ (ρ N) Z
lemma seedNear (i:Fin n) : skySeeds s o N i=C.seen (s i) (o N i):=by
    funext U
    unfold skySeeds MergeProof.item stepUp; dsimp only; rw [pull_one]; change C.O N p (s i).2 0 (Lattice.translate _ U)= C.O N p (s i).2 (o N i) U
    rw [C.translation 0,zero_add]
include hc

lemma correctStorm {j:ℕ}(hj:j≤N) : packStorm (Γ:=Γ) s (N:=N) (p:=p) (o N) j= gust C.path N p N (Accent.birth Γ (ρ N) (skySeeds s o N)) j hj :=by
  induction hj using Nat.decreasingInduction with
  | self=>
      rw [gust_base]; funext U; ext i :1
      let Y:= implants s (p:=p) (N:=N) (o N)
      change (Ride.bump _ i _)⁻¹ * Y.total i N (matrixField U) = _
      rw [Insertions.total_top,Insertions.source_eq,Accent.birth,Poly.part_smul, Accent.Mach, Extra.Trajectories.pass_fire]
      have hi : Ride.bump (C.S.a N) i Y.load≠0:= Finset.prod_ne_zero_iff.mpr (fun j _=> pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne'))
      simp_rw [seedNear,Ride.Product, ← implants_actual (x:=o N) (p:=p) (N:=N), (hc.wilson.starts N p).2]
      rw [mul_assoc (Ride.bump (C.path.S.a N) i Y.load)]
      change (Ride.bump (C.S.a N) i Y.load)⁻¹ *(Ride.bump (C.S.a N) i Y.load * _)= _ -- maybe assoc
      apply Eq.trans (inv_mul_cancel_left₀ hi _)
      rfl
  | of_succ j hj ih=>
      have hx:Integrable T (µ _):= (hatCont C N p Z (fun i=> (by unfold skySeeds; exact generics C N p (s i).1 (s:=fun _ : Fin n=> (s i).2) (fun j (_:Fin n)=> o j i) g i)) (show Continuous ((ρ N).eval) from by rw [(hc.wilson.starts ..).2]; exact bare_cont _) Γ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hr:Integrable (X (j+1)) (µ _):= ih.symm ▸ gust_live C.path N p N _ hx hj
      rw [gust_step C.path N p N _ hj,← ih]; funext U; ext i :1
      change pullDimes s (N:=N) (p:=p) (o N) i j U= _
      rw [weighDimes _ _ _ hj]
      exact congr_fun (push_get (C.path.levels.transition_mass ..) hr i).symm U

variable (hk:k<N) (hy:Migrating C.path k p N o) (hz:∀ i l,i ≠ l → ((C.path.levels.budget k).B)^2 ≤ separation (o k i) (o k l))
variable (hm:∀ i,C.ref (s i).1 ≤ k)(hcw:∀ i,0<w i) (hM:∀ i,w i * moneys C (s i).1 k N p (s i).2 ≤ fly C.path.levels (s i).1 k)
include W hk hy hz hm hcw hM
abbrev lines17 (N:ℕ):= harp C (fun i=> (s i).1) (fun i=> (s i).2) p N o g
abbrev ropes17 (N:ℕ):= chill C (fun i=> (s i).1) (fun i=> (s i).2) p N o g

set_option maxHeartbeats 600000 in
lemma openedStorm : Served (ρ k) (lines17 s o N k) (ropes17 s o N k) (X k) (o k) w (C.path.levels.budget k).supportExponent 1 ∧
    (Vault w (lines17 s o N k) (ropes17 s o N k) 3 1) ∧
    ∃ g':Fin n→ ℕ → Config G (C.side k p)→ℂ, (fun i=>MergeProof.profile (ρ k).activities (g' i))= ropes17 s o N k:=by
   let b:=C.path.levels.budget k
   obtain ⟨B,r,D,H⟩:= W.purchase; let T':= H.system
   let H':= (H.system.costs.pond (p:=p) (N:=N) (k:=k)) -- args?
   let U:= T
   let z i:= gust C.path N p N U i
   let w':= march w (near C.path.levels) k; have hh': w' k=w := marines k _ _ hcw
   have hi:Integrable U (µ _):=(hatCont C N p Z (fun i=> (by unfold skySeeds; exact generics C N p (s i).1 (fun j (_:Fin n)=> o j i) (fun _=> (s i).2) g i)) (show Continuous ((ρ N).eval) from by rw [(hc.wilson.starts ..).2]; exact bare_cont _) Γ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have hn:z N le_rfl=T:= gust_base ..
   have hv:∀ m,k ≤ m→∀ (h:m<N), z m h.le=(C.path.levels.clock.op m p).push ((ρ (m+1)).beta) (z (m+1) h):=fun m _ h=> gust_step C.path N p N U h
   have hx:Occupancy (o k) (r k):= fun i=> (Occupancy.of_injective (Edition.injected b.B (o k) b.B_pos hz) i).trans (H.system.back k)
   have hl:Drake Γ b.B (o k):= ⟨fun _ _ i _ j _ h=> hz i j h⟩
   have hp: (∀ i,w i * Spindle.paid C (s i).1 k N p (s i).2 ≤ fly C.path.levels (s i).1 k):= fun i=> (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (paid_pos ..) (col_ge C k)) (hcw i|>.le)).trans (hM i)
   obtain ⟨g',hg,hB⟩:= H'.past C δ N k p _ _ _ _ _ _ r D ε o g w hc.wilson (fun i=> hc.sections _) hm hk.le hx hy hl hp hcw
   have ha:= Frost.upper C.path _ _ _ D p N o w' (lines17 s o N) g' Z hc.wilson hk.le (desal C.path r k p N _ _ _ w hcw H'.stay Γ hy hl H'.mom hx) H'.night hg hv hn (hn.symm ▸ hi)
   have hr : tapes C.path p N g' k= ropes17 s o N k:= hB k le_rfl hk.le
   have hA:= (ha k le_rfl hk.le).2.2; rw [hh',hr,show topPitch C.path N k=b.supportExponent from if_neg hk.ne] at hA
   rw [correctStorm hc s o hk.le]
   refine ⟨hA,?_,⟨g' k, hr⟩⟩
   constructor <;> intro i x
   · change w i* ‖indexX C (s i).1 N p (s i).2 _ (1,false) k x‖≤ _
     apply le_trans (mul_le_mul_of_nonneg_left (scratch C (s i).2 k p N (g i) _ hc (hm i) hk.le x).1 (hcw i|>.le)); rw [mul_left_comm]; exact (mul_le_mul_of_nonneg_left ((hM i).trans (fly_le ..)) (by norm_num)).trans_eq (mul_one _)
   change (∑ j: MergeProof.Box _,w i*_) ≤ _; rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (scratch C (s i).2 k p N (g i) (fun j=>o j i) hc (hm i) hk.le x).2 (hcw i|>.le)).trans ((hM i).trans (fly_le ..))
end YM.RG17
