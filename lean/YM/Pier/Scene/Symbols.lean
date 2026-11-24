import YM.Pier.Scene.Motion
/-!
# Pay replacing multiple measured fields by physical sign of the hard jobs

Only the finite algebra. EVERY part which changes retains at least one
marked hard job. `µ` will be used on the actual scalar law on this side at TOP, after
bootstrapping the stamps. Use no per-period constants!
This budget OK with 1≤v and enough precision chosen earlier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe.Panoramic
open Pier.Scene Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{n:Side}{β:ℝ}
local notation "T" => Config G n

omit [Fintype I] [DecidableEq I] in
private lemma tsumPaid {J:Type} (u:Finset J) {F:J→ Config G n→ℂ} (he:∀ i∈u,Envelope (F i)) :
    moment β (fun x=>∑ i∈u,F i x)= ∑ i∈u,moment β (F i) := integral_finsetSum _ (fun i hi=>(he i hi).integrableC _)
private lemma toll_scalar {c:ℂ}(F:T→ℂ): moment β (fun x=>c*F x)= c*moment β F := integral_const_mul ..

variable {f : I→ Bool → Config G n → ℂ} {X Y : I → Config G n → ℂ}
    (s:Finset I) (z:I→ℂ) (hf:∀ i b, Envelope (f i b))
    (hx:∀ i x,X i x=f i false x + z i) (hy:∀ i x,Y i x = X i x - f i true x)
local notation "p" => fineJob
local notation "µ" => moment β

omit [Fintype I] in
private lemma normals {u v : Finset I} (_hs:Disjoint u v) {x:Config G n} :
    (∏ i∈u, f i false x)*(∏ i∈v, f i true x) = ∏ i ∈ u ∪ v, f i (decide (i∈v)) x:= by
  rw [prod_union _hs]; congr 1
  · refine Finset.prod_congr rfl (fun i hi=>?_); simp [Finset.disjoint_left.mp _hs hi]
  exact Finset.prod_congr rfl (fun i hi=> by simp [hi])

local notation "N" => Fintype.card I
variable {a v:ℝ} (ha:0≤a)(hL:∀ t:Finset I,t⊆s → ∀ g:I→Bool,
    (∃ i ∈ t,g i=true) → ‖moment β (fineJob (fun i=>f i (g i)) t)‖ ≤ a)
    (hc:∀ i,‖z i‖≤v) (hV:1≤v)
include hx hf hL hV hc ha
private lemma line_pay {t : Finset I} (ht : t ⊆ s)(he : t.Nonempty) :
    ‖µ (fun x=> ((-1 :ℂ)^t.card * ∏ i∈s\t, X i x) * ∏ i∈t, f i true x)‖ ≤ 2^N * (v^N * a) := by
  let g u : T→ℂ:= fun x=>(∏ i∈ u, f i false x)*(∏ i ∈ t,f i true x)
  let c (u:Finset I):= ((-1:ℂ)^t.card)*(∏ i∈ (s\t) \ u, z i)
  let pset:=(s\t).powerset; let w := v^N * a
  have hv:0≤w:= mul_nonneg (pow_nonneg (zero_le_one.trans hV) _) ha
  have hh : (fun x=> ((-1 :ℂ)^t.card * ∏ i∈s\t, X i x) * ∏ i∈t, f i true x) = fun x=> ∑ u∈pset,c u*g u x := by
    funext x; simp_rw [hx, prod_add]; rw [Finset.mul_sum,Finset.sum_mul]; exact sum_congr rfl fun i hi=> by unfold c g; ring
  rw [hh,tsumPaid _ (fun i _=>(Envelope.constC (c i)).mulC ((Envelope.prodC i _ (fun j _=>hf j false)).mulC (Envelope.prodC t _ (fun j _=>hf j true))))]; simp_rw [toll_scalar]
  have hp : (pset.card:ℝ) ≤ 2^N:=by unfold pset; rw [card_powerset]; exact_mod_cast (show 2^((s\t).card) ≤ (2:ℕ)^N from pow_le_pow_right₀ (by omega) (card_le_univ ..))
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ _i ∈ pset, w := by
       refine sum_le_sum fun i hi=>?_
       have hf := mem_powerset.mp hi
       have hx : Disjoint i t:= Finset.disjoint_left.mpr fun j hj hh=> (mem_sdiff.mp (hf hj)).2 hh
       have hG: ‖µ (g i)‖ ≤ a:=by
          let u (j:I):= decide (j∈t); obtain ⟨y,hy⟩:=he
          rw [show g i= fineJob (fun j=> f j (decide (j∈t))) (i∪t) from funext fun _=> normals hx]
          exact hL _ (union_subset (hf.trans sdiff_subset) ht) u ⟨_, mem_union_right _ hy, by simp [u,hy]⟩
       have hr: ‖c i‖ ≤ v^N:= by
          unfold c; simp_rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_prod]
          refine (prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>hc j)).trans ((prod_const v).le.trans (pow_le_pow_right₀ hV (card_le_univ ..)))
       rw [norm_mul]; exact mul_le_mul hr hG (norm_nonneg _) (pow_nonneg (zero_le_one.trans hV) _)
    _ = (pset.card:ℝ)*w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hp hv

include hy
lemma payMany : ‖moment β (fineJob X s)- moment β (fineJob Y s)‖ ≤ 2^N * (2^N * (v^N * a)) := by
  let F (t:Finset I) (x:T) := ((-1 :ℂ)^t.card * ∏ i∈s\t, X i x) * ∏ i∈t, f i true x
  have he : fineJob Y s = fun x=> ∑ i∈s.powerset,F i x:= by funext x; unfold fineJob; simp_rw [hy]; exact prod_sub _ _ s
  let P:= s.powerset.erase ∅
  have hh : F ∅ = fineJob X s:= by ext; simp [F,fineJob] -- ext issues
  let c0:=2^N * (v^N * a); have hv:0≤c0:=by unfold c0; positivity
  have hy(i): Envelope (X i):=by
     have h:= (hf i false).addC (Envelope.constC (X:=T) (z i)); exact (funext (hx i)).symm ▸ h
  have hZ(i): Envelope (F i):= ((Envelope.constC _).mulC (Envelope.prodC _ _ (fun i _=> hy i))).mulC (Envelope.prodC _ _ (fun i _=>hf i true))
  rw [he,tsumPaid _ (fun i _ => hZ i), ← Finset.add_sum_erase _ _ (empty_mem_powerset s),hh,← sub_sub]; rw [sub_self,zero_sub,norm_neg]
  have hp(i:Finset I)(hi:i∈P): ‖moment β (F i)‖ ≤ c0:= line_pay s z hf hx ha hL hc hV (mem_powerset.mp (mem_of_mem_erase hi)) (nonempty_iff_ne_empty.mpr (ne_of_mem_erase hi))
  calc _ ≤ ∑ _i∈ P,c0 := (norm_sum_le ..).trans (Finset.sum_le_sum hp)
       _ = (P.card:ℝ)*c0:= by simp
       _ ≤ _:= mul_le_mul_of_nonneg_right (by
            have ht : P.card ≤ 2^N:= (Finset.card_le_card (erase_subset _ _)).trans ((Finset.card_powerset s).le.trans (pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) (Finset.card_le_univ ..)))
            exact_mod_cast ht) hv
end YM.OPE.Strobe.Panoramic
