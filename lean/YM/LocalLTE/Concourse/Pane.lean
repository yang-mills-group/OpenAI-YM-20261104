import YM.LocalLTE.Concourse.Memo
/-! Estimating centered memory. True charge excludes unit. Future queries at the same points. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Concourse
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Motion
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{F:Labels.Frame G 0}
local notation "O" => H.rep N p m
local notation "P'" => H.rep N p (m+1)
local notation "κ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "κ'" => Real.sqrt (H.levels.clock.forcedAllowance (m+1))
open LocalLTE.Drift Planned.GuardedAtom.Guard Lotus
variable {K S w:ℕ} {k:ℕ→ℕ}{s s' y: ℕ→ℝ}{πt l:ℝ}
variable (D:SectionData F)(A:Hol G)(W₀:Gateway F A (H.rep N p (m+1)) (H.S.side m p))
    (T:Etching D A (H.rep N p (m+1)) (H.S.side m p) k K S l)
    (Z:Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities) (P : Coefficient F (H.S.side (m+1) p)) (E:ℕ→ Coefficient F (H.S.side (m+1) p))
local notation "X'"=> rack Z (Concourse.memo F.e0 P)
local notation "g"=> H.S.side m p
variable {t:ℝ} (U:Syllabus H N p m A (rack Z (Concourse.memo F.e0 P)) t) (V: Paper (H:=H) (N:=N) (m:=m) (p:=p) D A E K k S l s s')
noncomputable abbrev account (j:ℕ)(hj:j≤K): Coefficient F (H.S.side m p):= Drift.auction D A (rack Z (Concourse.memo F.e0 P)) W₀ T U V 0 j hj
local notation "M"=> Concourse.honour A W₀ Z P U
local notation "I"=> Concourse.ticketP A W₀ Z P U
local notation "Qua"=> account D A W₀ T Z P E U V
set_option quotPrecheck false
structure Center {n:Side}(Q: Rep G n)(P: Coefficient F n)(E:ℕ→ Coefficient F n)(k:ℕ→ℕ)(K S:ℕ)(l κt:ℝ)(s s' e:ℕ→ℝ) : Prop where
    slip j : j ≤ K → Exhibition D l S (k j) A Q (memo 0 P) (E j) κt (s j) (e j)
    lift j : j<K → Patrons D l S (k (j+1)) Q.p (Vinca.decrement (E (j+1)) (E j)) (s' j)
    centered j: j≤K→ (E j).x=0
variable {T} (C:TariffX)(hx:Works D A (H.rep N p (m+1)) (H.rep N p m) w W₀ T (Real.sqrt (H.levels.clock.forcedAllowance m)) C)(hp:F.coeffSize ((Vinca.unitP F H p m).x) ≤ C.token.issue) (hc:Center D A (H.rep N p (m+1)) P E k K S l (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) s s' y)
local notation "ν"=> (fun i=> (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))*(y i+y i))
local notation "sF" a:max=> (fun i=> C.slip a s s' y (i+1) + C.slip a s s' y i)
section moving
variable (T)
noncomputable def outgoing (j:ℕ):Coefficient F (H.S.side m p):= if h:j≤K then memo 0 (account D A W₀ T Z P E U V j h) else Extra.Histories.primary 0 0
noncomputable def reserve (u:F.Coeff):= ((Qua K (le_refl K)).x - F.e0)+u
end moving
local notation "S₀"=> outgoing D A W₀ T Z P E U V
include hp hx hc
lemma hailed (u:ℝ)(hu:t ≤u): (∀ i:ℕ,∀ hi:i≤K, Exhibition D l w (k i) A (H.rep N p m) I (Qua i hi) κ (C.peak u s s' y i) (C.delta u s s' y ν i)) ∧ ∀ j,j<K→ ∀ h:j<K,k j ≤ k (j+1)→ Patrons D l w (k (j+1)) ((H.rep N p m).p) (decrement (Qua (j+1) h) (Qua j h.le)) ((sF u) j):=by
   let u0:=rack Z P; let X₀:= X'; have hκ' := Real.sqrt_pos.mpr (forcedPos H.levels (m+1))
   have hQ:SumBudget (fun i=>(P'|>.p.mass ((X').support i) (U.a i))) u:=by refine ⟨U.front.1,U.front.2.1,U.front.2.2.trans ?_⟩; have h0:0≤U.k:= nonneg_of_mul_nonneg_right (sumBudget_credit U.pier) hκ'; exact ((le_add_of_nonneg_right h0).trans (U.uniont.trans hu))
   have hs j (hj:j≤K): Local.ForceCost (H.rep N p (m+1)).p (H.rep N p (m+1)).activities X₀.forced (ν j):=by
        have hv := hc.slip j hj; let d:=decrement (memo (0:F.Coeff) P) (E j); have ht:d.forced=(memo F.e0 P).forced:=by change _-(E _).forced=_; rw [hv.stock.forced,sub_zero]
        have hg:(rack Z d).forced=X₀.forced:=by unfold X₀ MergeProof.rack MergeProof.stowK; rw [ht]
        obtain ⟨s₂,r',hh,_,hm',_,hk',q,hq,hv'⟩:=MergeProof.keeps Z _ (hv.fee.bound le_rfl); rw [← hg]; exact ⟨q,⟨hq.1,hq.2.1,hq.2.2.trans (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left hh).trans hm') hκ'.le)⟩,hv'⟩
   choose t ht hT using fun (j:ℕ) (hj:j≤K)=> (hc.slip j hj|>.fee.regular)
   let b i q:= if h:i≤K then t i h q else 0
   have ht'(i)(h:i≤K):b i=t i h:=funext fun _=>dif_pos h
   have hZ(i)(h:i ≤ K): SumBudget (fun j=>(H.rep N p (m+1)|>.p.mass (X₀.support j) (b i j))) (y i):=by rw [ht' _ h];exact ht i h
   have hX(i:ℕ)(ht:i ≤ K)(j): (H.rep N p (m+1)).p.supBounds 0 (X₀.support j) (X₀.regular j-(E i).regular j) (b i j):=by rw [ht' _ ht]; exact hT i ht j
   have he:X₀.support=(E 0).support:=(hc.slip 0 (Nat.zero_le _)).layout
   constructor
   · intro j hj; obtain ⟨q,hq,hp'⟩:= hs j hj; exact Drift.ballet D A _ W₀ T U V 0 w b C hx hp he hX j hj hQ hZ q ν hq hp'
   intro j _ hK h; obtain ⟨q,hq,hp'⟩:= hs j hK.le; exact Drift.bridgeP D A _ W₀ T U V 0 w b C hx hp he hX j hQ hZ q hp' q hp' hK h
variable {η v:ℝ}
lemma center (u:ℝ)(hu:t≤u)(d:F.Coeff)(hD:F.coeffSize (P.x-d) ≤ η)
    (r s₀ s₁:ℕ→ℝ)(hC:∀ i,i ≤ K→ C.peak u s s' y i ≤ r i) (ht:∀ i,i ≤ K → C.delta u s s' y ν i ≤ s₀ i)
    (hh:∀ i,i<K→ C.slip u s s' y (i+1)+C.slip u s s' y i ≤ s₁ i) (hw:∀ i,i<K→ k i≤ k (i+1)):
    Center D A (H.rep N p m) M S₀ k K w l (Real.sqrt (H.levels.clock.forcedAllowance m)) r s₁ s₀ ∧ F.coeffSize ((M).x-reserve D A W₀ T Z P E U V d) ≤ s₀ K + η:=by
   obtain ⟨he,hX⟩:= Concourse.hailed D A W₀ Z P E U V C hx hp hc u hu -- T implicit
   refine ⟨⟨fun i hi=>?_,fun i hi=>?_,fun i hi=>?_⟩,?_⟩
   · rw [outgoing,dif_pos hi, show memo 0 M=memo 0 I from rfl]; exact Concourse.disrobe ((he i hi).pledge (hC i hi) (ht i hi))
   · unfold outgoing; rw [dif_pos (show i+1≤K from hi),dif_pos hi.le, memo_off]; simp only [sub_self]; apply Concourse.stripped; exact (hX _ hi hi (hw _ hi)).priced (hh i hi)
   · rw [outgoing,dif_pos hi]
   let j:= Qua K (le_refl K); let m0:= I; have hx:= (he K le_rfl|>.canon).trans (ht K le_rfl);
   change F.coeffSize ((m0.x-F.e0+P.x)-(j.x-F.e0+d))≤_ ; rw [show m0.x-F.e0+P.x-(j.x-F.e0+d)=(m0.x-j.x)+(P.x-d) from by abel]; exact (Size.add ..).trans (add_le_add hx hD)
-- memory buying. prior Paint certificates purchase aspirant sector powers.
omit hp hx
lemma Center.licenses : Nonempty (Paper (H:=H) (m:=m) (p:=p) (N:=N) D A E K k S l s s'):= Drift.scrolls D A _ hc.slip hc.lift
omit hc
variable {Q':Rep G (H.S.side m p)} {Y:Coefficient F (H.S.side m p)}{Gx : ℕ → Coefficient F (H.S.side m p)}
lemma Center.trim (h:Center D A Q' Y Gx k K w l πt s s' y) (i:ℕ)(ht:w ≤ i): Center D A Q' Y Gx k K i l πt s s' y:= by
   refine ⟨fun j hj=> (h.slip j hj).large le_rfl le_rfl le_rfl ht,fun j hj=>?_,h.centered⟩; convert! (h.lift j hj).raise («a»:=0) (by simp) ht le_rfl using 1; rw [add_zero]
end YM.LocalLTE.Concourse
