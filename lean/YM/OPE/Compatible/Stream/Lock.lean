import YM.OPE.Compatible.Stream.Pool
/-!
# Last-window exponential
Use only on same chosen penalty and kernel on virtual hops. Terms v,w throughout independent of L beyond previous pre-requisites on the genuine histories.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Frequency
open Function Filter Set Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate
open Flight
variable {L:Side} {j k:ℕ} {η x U a B:ℝ}
local notation "T"=> TypeFace 2
variable (C:KernelChoices)
-- fixed aux block at stage j
lemma season (j:ℕ)(hj:4 ≤ j): ∃ η U a D:ℝ,0<η∧0<U∧0 < a ∧ Covers η C.penalty U j j ∧ (∀ v:Train j, (pink C.penalty v).strip η a)∧∀ i:Axis,(pathJet T [i]).strip η D:=by
   obtain ⟨σ,Q,h,hQ,hP⟩:= stockroom C.penalty C.penalty_pos hj hj
   obtain ⟨a,D,ha,hD,g⟩:= (heart_saves C.penalty C.penalty_pos hj (fun P:Train j=>P)).1.uniform
   obtain ⟨s,V,hV,hg,hx⟩:= staple (κ:=Axis) (fun i s V=> (pathJet T [i]).strip s V) (fun x=> by
       obtain ⟨η,C,h,h'⟩:=jet_whole T [x]; exact ⟨η,max C 0 +1,h,lt_of_le_of_lt (le_max_right ..) (by linarith),strip_mono h' le_rfl (le_of_lt (lt_of_le_of_lt (le_max_left ..) (by linarith)))⟩) (fun i _ _ _ _ h ha hu hc=> strip_mono h ha hc)
   let z:= min σ (min s a); have hz:0<z:=lt_min h (lt_min hV ha)
   refine ⟨z,Q,D,V,hz,hQ,hD,fun i l hl=>strip_mono (hP _ _ hl) (min_le_left ..) le_rfl,fun v=> strip_mono (g v) ((min_le_right ..).trans (min_le_right ..)) (by simp),fun i=> strip_mono (hx i) ((min_le_right ..).trans (min_le_left ..)) le_rfl⟩

-- ancestry state
variable {C}{Z:Patch} {d:ℕ} {R:Row T T}
abbrev tow (R:Row T T)(η c:ℝ):=R.strip η c∧ R.read 0=0
abbrev ded (s U D:ℝ):= lobe.length * (Fintype.card T:ℝ)^3 * yieldW s*D*U^2
abbrev ship (Z:Patch) (P:Train Z.J) : Flight Z.J Z.J:=⟨Z.L,Z.odd_side,Z.coarse,Z.order_cut,le_rfl,by omega,P⟩
def folder (Z:Patch)(P:Train Z.J) :ℕ→Train Z.J
| 0=>P
| n+1 => ((ship Z (folder Z P n)).land)
variable (h:0<η) (hp:Covers η C.penalty U Z.J Z.J)(he:∀ x:Axis,(pathJet T [x]).strip η a)
include h hp he
lemma purse {b:ℝ}(hb:0≤b)(H:tow R η b)(hh:ded η U a/(Z.L.val:ℝ)≤1/2){p q:Train Z.J}(hq:Key C p q R) : ∃ R:Row T T,tow R η (b/2)∧ Key C ((ship Z p).land) ((ship Z q).land) R := by
   let P:=ship Z p; let Q:=ship Z q
   have hr:tow (sling Q C.penalty (P.psi C.penalty) R) η (b/2):=by
      have heq :(P.psi C.penalty).strip η (U/Z.L.val^2):=hp P [] (by simp)
      refine ⟨strip_mono (band Q _ h hp H.1 heq he) le_rfl (show ded η U a/(Z.L.val:ℝ)*b ≤ b/2 from ?_), silence Q _ h hp H.1 heq⟩; linarith only [mul_le_mul_of_nonneg_right hh hb]
   exact ⟨_,hr,pack_next C Z p q le_rfl (by omega) Z.order_cut h hp hq H.1 H.2⟩
lemma last_window {b:ℝ}(hb:0≤b)(H:tow R η b)(hh:ded η U a/(Z.L.val:ℝ)≤1/2){p q:Train Z.J}(hq:Key C p q R) (n:ℕ) : ∃ U:Row T T,tow U η ((1/2:ℝ)^n*b)∧ Key C (folder Z p n) (folder Z q n) U := by
    induction n with
    | zero=>simp only [pow_zero,one_mul]; exact ⟨R,H,hq⟩
    | succ n ih=>
      obtain ⟨A,ha,hz⟩:=ih
      obtain ⟨B,hB,ht⟩:= purse h hp he (mul_nonneg (pow_nonneg (by norm_num) _) hb) ha hh hz
      rw [pow_succ,show _ * (1/2:ℝ) * b = ((1/2:ℝ)^n*b)/2 from by ring];exact ⟨B,hB,ht⟩
omit hp he
-- first
variable (C)
lemma starting (hj:4≤j) {p q: Train j} (ht:(pink C.penalty p).strip η a) (hz:(pink C.penalty q).strip η a) : ∃ R:Row T T,tow R η (2*a) ∧ Key C p q R:=by
   let R:= pink C.penalty (j:=j); let P:= minusRows (R p) (R q)
   have he(v:Train j): (R v).read 0=1:=by
      have hP : (0:Momentum)∈ baseCube:=⟨by unfold physical; simp,by intro i; simp [Real.pi_pos.le]⟩
      rw [show (R v).read _=_ from (heart_true C.penalty C.penalty_pos hj v).1.echo 0 hP,pulse, Train.bend_zero, inv_one,one_smul]; simp only [Train.bulb_zero,inv_one]; exact mask_one ..
   refine ⟨P,⟨by rw [two_mul]; exact strip_minus ht hz,?_⟩,fun n=>?_⟩
   · unfold P; rw [read_less (Whole.safe (A:=R p) ⟨_,_,h,ht⟩) (Whole.safe (A:=R q) ⟨_,_,h,hz⟩) (show physical 0 by unfold physical;simp),he,he,sub_self]
   rw [show P.acts n= (R p).acts n - (R q).acts n from acts_minus h.le ht hz n]; unfold K; rw [Matrix.mul_sub,Matrix.sub_mul]
end YM.Next.Free.Frequency
