import YM.MergeProof.North.Anise
import YM.Frontier6.Multi.Gather.Liturgy
import YM.Frontier6.Multi.Scene.Arbor

/-!
# Nonterminal compaction

Generalization of North/Anise to arbitrary concentration. Maintains coherences
*also on monomials of the remaining slots*, hence the `Serves`, not `Served`.
Complete census at both input and output. No disallowments of interactions
within the puffed aperture. Fresh anchor occupancy cost for **all old** names
moved to their designated output locations, not just output occupancy.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}{R:Rep G n}{v:V}{t a x b: ℝ}
variable {A₁ A₂:Type}[DecidableEq A₁][DecidableEq A₂][Fintype A₁][Fintype A₂]
variable {P:V→Motion}{E:V→Site n}{β:V→Equiv.Perm V}{μ:Live V A₁→Site n}
variable {g:Live V A₁→ Config G n→ℂ}{k:Live V A₁→ℕ→ Config G n→ℂ} {r:Live V A₁→ℂ}{J:Live V A₁→ℝ} {h':Config G n→Poly (Now V A₁)} {Z y c q d z:ℝ}
variable (π:Concentrate A₁ A₂) {w:Live V A₂→ℝ} (s l:ℕ)(η T Z:ℝ)
set_option quotPrecheck false
local notation "U!"=>Now V A₂
local notation "y!"=> Salt.scent R.p.B s (R.p.supportExponent+c) T η a b
local notation "W₁"=>Salt.tow J (R.p.supportExponent+c) η l
local notation "group"=> batt (V:=V) π
local notation "λ!"=> μ ∘ (group).seat
lemma grafted (A:Arsenal R)(h:Arc R g k h' v P E β μ J (R.p.supportExponent+c) (R.p.supportExponent+q) a b x r)(hr:R.activities.Valid R.p z d)(he:∀ i,i≠v → β i v=i ∧ ∀ j:A₁, μ (i,j)=affine (P i).1 (E i) (μ (v,j))∧r (i,j)=scalar (P i) (r (v,j))) (hw:∀ i,0<J i)(hv:Occupancy μ s)(h0:Occupancy ((λ!) ∘ (group).hit) s)(ht:0≤T)(hy:∀ i,J i*‖r i‖ ≤ T)(hm:0<R.p.B)(hX:0<η)(hY:η≤1)(hS:∀ i:Live V A₁,coverNumber R.p.B ({μ i,(λ!) ((group).hit i)}:Support n)≤ l)(hc:0≤ c)(hq:c≤ q)
    (hit:∀ U,R.eval U≠0)(hu:∀ i,w i=∏ j∈(group).fiber i,W₁ j)(hJ: ((R.p.B + R.p.B + 1 : ℕ):ℝ)^4*(y!) ≤ c)(hξ: Real.exp (y!)-1≤ Z) :
    ∃ g:Live V A₂→ Config G n→ℂ,∃ k:Live V A₂→ℕ→ Config G n→ℂ,
       Serves R g (fun i=>profile R.activities (k i)) (fun U=>(group).reap (h' U)) v P E β (λ!) w R.p.supportExponent Z ∧ (∀ i,Dominated (k i) ∧ Blade R ((λ!) i) (g i) (profile R.activities (k i)) 0 (4*(Z/w i))) ∧ May v P E β g (fun i=>profile R.activities (k i)) 0 :=by
    obtain ⟨F',K,ψ,hΨ,-,hF,hK,hF',hK',hp,hZ,-,rfl⟩:=h.see
    let S:Salt (group) G n:= ⟨μ,r,F',K⟩; let t:=R.p.threshold; let D:=S.vessel t; have hB : S.Breeze t:=⟨hF',hK'⟩; let V₀ i U:=S.mount t i U; let V₁ i U:=S.soil t i U
    have hv' := S.rate J t (R.p.supportExponent+c) T η s _ l hw hv hy hm hX hY (fun i=>(show coverNumber _ {(λ!) ((group).hit i),μ i}≤ l from by rw [pair_comm];exact hS i)) h0 a b ht hF (hK.shrink (by linarith only [hq]) le_rfl hw) (add_nonneg R.p.exponent_pos.le hc)
    have hM:= S.turn t hB; have hE := S.wet _ hB; have hW := Salt.towP _ (R.p.supportExponent+c) _ l hw hX; obtain ⟨hb,hh⟩:= D.carries t hE W₁ w R.p.supportExponent c (y!) R.p.B hv' R.p.exponent_pos.le hW hu hJ
    have hWp i:0 < w i:=by rw [hu]; exact prod_pos (fun i _=>hW _)
    have ht:=hb.shrink le_rfl hξ hWp; have hT:=hh.shrink le_rfl hξ hWp
    let y' U := Mach (U!) 0+ ∑ i,V₀ i U; let gy(v:Live V A₂)(U):=(y' U).part ((U!).fire v)
    obtain ⟨k,hR,hS',hC,hJ'⟩:= Ribbons.plume (F:=V₀) (K:=V₁) A hr (fun i=> D.clearBurn t hE hM i) (fun i=>D.cloudy t hE hM i) ht hT hWp (fun i U=>(S.taxed t U hB i).trans (hZ ..)) hit 0
    have hTw (i:V)(hi:i≠v):Twin S t (P i) (E i) v i (β i):=⟨(he i hi).1,fun j=>(he i hi|>.2 j).1, fun j=>(he i hi|>.2 j).2,fun p h j U=> (hp i hi|>.2 U).1 j p h, fun p h j U=>(hp i hi|>.2 U).2 j p h⟩
    have hf (i:V) (b':A₂)(hi:i≠v): drum (β i) ((U!).fire (v,b'))=(U!).fire (i,b'):=by rw [go_one,show nome _ (v,b')= (i,b') from Prod.ext (he i hi).1 rfl]
    refine ⟨gy,k,?_,fun i=>⟨(hR i).1,(by rw [show 4*(Z/w i)=2*(Z/w i)+2*(Z/w i) from (by ring)]; exact (hR i).2)⟩,fun i hi=>?_⟩
    · refine ⟨_,_,hC,Towed.sift ht,Towed.sift hT,fun i hi=>?_,Eq.trans ?_ hJ'⟩
      · refine ⟨(he i hi).1, fun U=>⟨fun j=>Harps ((Twin.twines (hTw i hi) U).1 j),fun j=>Harps ((Twin.twines (hTw i hi) U).2 j)⟩⟩
      funext U; unfold play; dsimp only; rw [map_smul,Ribbons.blank_mach,zero_add,S.yields _ U hB]
    refine ⟨(he i hi).1,fun b'=> ⟨?_,?_, (scalar_z _).symm⟩⟩
    · funext U; unfold gy stepUp y'; simp_rw [Ribbons.blank_mach,zero_add,Poly.part_sum]; rw [Float.summer,← Equiv.sum_comp (sky (P i) (E i))]
      refine Finset.sum_congr rfl (fun j _=>?_); rw [← hf i b' hi]; exact (Twin.twines (hTw i hi) U).1 j _ ((which ..).2 rfl)
    funext j U; unfold floatUp stepUp; obtain ⟨j,h⟩:= (puff (P i) (E i)).surjective j; rw [← h,Equiv.symm_apply_apply]; dsimp only; rw [←hS',← hS']; rw [←hf i b' hi]; exact (Twin.twines (hTw i hi) U).2 j _ ((which ..).2 rfl)
end YM.MergeProof.Canopies
