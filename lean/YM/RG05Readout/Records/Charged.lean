import YM.RG05Readout.Records.Chains
import YM.RG05Readout.Aligned.Density
/-!
# Terminal charge on complete marked crop, projected null + true volume.

Receipt is common across tests given Signature. Census history Lecture is an
output from Storage and purchases. Product genealogy uses many V only in
threshold masks or allowed Bush. Normalize at same law after all budgets,
no volume-independent lower bound assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open Records.Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d ℓ:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g:ℕ}
variable (h:C.Makes){D: Address.Rail C} {ψ:ℕ→ℕ} {w:Worth} {B:ℕ→ℕ→ℝ}
    (Y:OPE.Package C w ψ D)(hC:Storage C D) (hS:Cater C D)
set_option quotPrecheck false
local notation "λ₀"=> C.path.levels.clock
local notation "X!"=> C.side N p
local notation "K!"=> C.side (n+1) p
local notation "Z!"=> C.path.levels.budget
local notation "ν"=> C.path.levels.clock.J
local notation "R!"=> C.path.rep N p
local notation "Kd"=> Fintype.card (Color V)
local notation "ξ!"=> n+1
variable (y: V→Site (C.side (n+1) p))(s:V→ℕ)(F:V→Body)
variable (T':(i:V)→Palette C (s i)) (P:Sight C d p)(S:Emblems C d) (A:(i:V)→Sight C (s i) p)(U:(i:V)→Emblems C (s i))
variable (hm:n+1 < m)(hk:m≤N)
local notation "hN"=> hm.le.trans hk
local notation "s₁"=> (fun j:V=>Many.point (U j) (T' j) m N)
local notation "J₁"=> bunchG (C:=C) (N:=N) y s F s₁
local notation "x!"=> dyes C (n+1) N p hN J₁
variable (w':PulseC)
variable {e E Q:ℝ} {R:ℕ→Palette C d}{T:∀ i:ℕ,Tape G (C.side i p)}
local notation "r"=> Shadow.repayment S R b n
local notation "M₁"=> finer S (Nat.le_trans (Nat.le_succ n) hm.le) (R n- Shadow.advances S R b n)
variable (hp:Awake D B b d)(hv:Spine D B h b p d N P S)(hA:∀ i:V,Spine D B h (n+1) p (s i) N (A i) (U i))
    (hy: Priced d w' 1) (ht:b ≤ n) (hξ:Signature C p b n N d h D P (amplitude C n N p d w' (dyes C (n+1) N p (hm.le.trans hk) (bunchG y s F (fun j:V=> Many.point (U j) (T' j) m N)))) e R T)
lemma repack : let z:= M₁; Many.point S z m (n+1)= r:=by
    intro z; unfold Many.point; rw [dif_neg (show ¬m < n+1 from not_lt.mpr hm.le)]
    unfold z; rw [Many.sumwalk S n.le_succ hm.le,Address.finer_next (le_refl n),base_value, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; rfl

def rebirth (C:Family G)(d n p N:ℕ)(h:n+1≤N)(w:PulseC)(M:Palette C d)(f:Goods G (C.side N p)): Bin G (C.side N p):= fun φ=> w φ • f - crops C N p N d le_rfl (precinct C p N d M) (n+1) h φ
local notation "f!"=> rebirth C d n p N hN w' (Many.point S M₁ m N) J₁
variable {X:ℕ→Type}[∀ i, Fintype (X i)][∀ i,DecidableEq (X i)] (Z:Planner C p b X I) (F':∀ i:ℕ,X i→Body)
local notation "e'"=> Z.labelY
local notation "M₀"=> X (n+1)
local notation "V!"=> Unit × Root (X (n+1))
local notation "q!"=> F' (n+1)
local notation "E!"=> Z.motion ∘ Z.labelY (n+1)
local notation "o₀"=> Z.supportX
local notation "U₀"=> brisk (e' (n+1))
local notation "c₀"=> o₀ (n+1)
local notation "ν₀"=> fee C m ξ! ℓ k Kd Q
local notation "F₁"=> safe C d n e ν₀ (4*(1/ν₀))
local notation "T₀"=> swell hN Z (fun _=>d) (fun _=>f!) F'
local notation "T₁"=> (coarse_base (Z.supportX (n+1)) E! y s F q! (Many.point S M₁ m N) s₁ hN)
local notation "Q₀"=> birth U₀ (C.path.rep N p N) T₁
local notation "Q₁"=> gust C.path N p N Q₀ (n+1) hN
local notation "Γ"=> turnL (X ξ!)
local notation "Δ"=> Prod.fst ∘ turnL (X ξ!)
local notation "ψ!"=> Shadow.pens Z (Γ) (F' ξ!) w'
-- after signing. uses actual descendant profiles
omit [DecidableEq V] [DecidableEq I] [Fintype I] in
lemma harvest_p : T₀ (n+1)=Many.combine (Δ) ψ! T₁:=by
   funext i; let f':= fun i' : M₀ => F' (n+1) i'; let K':=(Γ); let a:= c₀ i; let g:= E! i; let v:= (C.S.toDepth hN p).embed a
   have he: uniform C ξ! p N d hN f! ξ! a g (f' i)=stepUp g v (f! (f' i)):=by unfold uniform; rw [dif_pos le_rfl,crops_head]
   unfold Many.combine; rw [← Equiv.sum_comp K'.symm]; simp only [Fintype.sum_prod_type,Fintype.sum_bool]; rw [sum_eq_single i]; rotate_left
   · intro i' _ hv; simp only [Function.comp_apply,show K'=Γ from rfl,Equiv.apply_symm_apply]; rw [if_neg hv, if_neg hv]; simp
   · simp
   simp only [Function.comp_apply, show K'=Γ from rfl,Equiv.apply_symm_apply,if_true]
   change uniform C ξ! p N d hN f! ξ! a g (f' i)=_ ; rw [he]; unfold rebirth; rw [rot_sub,rot_scalar, show ψ! ((Γ).symm (i,false))=(-1:ℂ) from rfl, neg_smul,one_smul,sub_eq_add_neg]; congr 2
   -- align second
   change _= clinic C p N d (Many.point S M₁ m N) (n+1) a g (f' i); unfold clinic uniform; rw [dif_pos hN]
omit [DecidableEq V] [DecidableEq I] [Fintype I] [(i : ℕ) → Fintype (X i)] [(i : ℕ) → DecidableEq (X i)] in
lemma swell_visit (i: X b): Continuous (T₀ b i):=by
   have hq(f:Body): Continuous (f! f):=by
      unfold rebirth; apply Continuous.sub; exact (continuous_finsetProd _ (fun i _=>clinic_cut ..)).const_smul _; let z:= Many.point S M₁ m N; suffices h: clinic C p N d z (n+1) 0 (1,false) f=crops C N p N d le_rfl (precinct C p N d z) (n+1) hN f by exact h ▸ clinic_cut z _ _ _ -- edit
      unfold clinic uniform; rw [dif_pos hN,show (C.S.toDepth hN p).embed 0=0 from (C.S.toDepth hN p).root.map_zero]; exact MergeProof.Ribbons.stepid _
   unfold swell uniform; split
   next hi => have hc:= crops_cut (d:=d) hq hN hi (F' b i); unfold stepUp Motion.scalar; split; exact (hc.comp (continuous_pull ..)).star; exact hc.comp (continuous_pull ..)
   next hi=> exact continuous_const
local notation "H₀"=> (fun i:ℕ=> Many.Lift (Stock.census I) (e' i))
include h Y hC hS hp hv hA hξ ht hy
set_option maxHeartbeats 500000 in
lemma signs (hQ: Campaign (e' (n+1)) (Z.supportX (n+1)) E! y s F (F' (n+1)) T' k d ℓ m Q) (hr:size (M₁) ≤ Q)(hP: ∀ i:X b,Cap (d+2) (F' b i) 1) (hZ: PreparedA Z F' b (n+1) le_rfl)
    (hU:d+3 ≤ C.path.levels.clock.J n)(hY:∀ i,b ≤ i → Pin C i d)
    (hO: ∀ i,b ≤ i → i ≤ n → Occupancy (Z.supportX (i+1)) (apron C.path.levels i) ∧ Occupancy (((C.path.levels.clock.op i p).ratio.parent) ∘ Z.supportX (i+1)) (apron C.path.levels i))
    (hG:∀ i,b ≤ i→ i < n → Drake (H₀ (i+1)) (C.path.levels.budget i).B (((C.path.levels.clock.op i p).ratio.parent) ∘ Z.supportX (i+1))) :
    0< F₁ ∧ ∀ s:(Lift (Stock.census I) (Z.labelY b)).Mode, ‖C.omega N p (fun U=> ∏ i∈s.val,T₀ b i U)‖*(focus C F₁ n b)^s.val.card ≤ Real.exp ((Fintype.card (Site (C.side b p)):ℝ)* Vac.treasury C.path.levels b+ Fintype.card (X b)*(2*salary C b d+2)):=by
     obtain ⟨hρ,hX,hF,hI,hη⟩:= steered h Y hC hS (e' (n+1)) c₀ E! y s F (F' ξ!) Q T' P S A U hm hk (Records.Spine.tail h P S hv (ht.trans n.le_succ)) hA hQ M₁ hr
     let x:= Q₁; have hΨ: LotusNotes (V:=P) (S:=S) (b:=b) (Y:=R) (N:=N) (θ:=Γ) x! Z F' hF (4*(1/ν₀)):= ⟨fun i=> (hη i).2,fun i=>by dsimp only; rw [← repack S hm]; exact (hη i).1⟩
     have hR : License (H₀ ξ!) U₀ (Δ):= licensed (e' ξ!); let A':= fun Y=> feed ψ! hR (x Y)
     obtain ⟨f',hf,hf'⟩:= reels_write (H:=H₀) Z (fun _=> d) (le_refl b) (ht.trans n.le_succ) (fun i hi _=> by
       rw [show Z.labelY (i+1)=_ from funext fun x=> show Z.labelY (i+1) x = (Z.labelY i ∘ Prod.fst ∘ Z.narrows i hi) x from Z.loyal i hi x]; exact Many.Lift_retrieve _ _ _) A' N
     have hθ: T₀ (n+1)=Many.combine (Δ) ψ! T₁:= harvest_p y s F T' S U hm hk w' Z F'
     obtain ⟨he',hQ0⟩:= blended T₁ ψ! hR hN hX
     have hqf : f' (n+1)=gust C.path N p N (birth (H₀ ξ!) (R! N) (T₀ (n+1))) ξ! hN:=by rw [hθ]; exact hf'.trans hQ0.symm
     rw [← hθ] at he'
     obtain ⟨hx,hu⟩:= descend h hp hv hS hC x! w' hξ ht (Nat.lt_of_succ_le hN) Z F' (Γ) hF x hρ hI hΨ hP hZ hU hY hy (by positivity) hR hO hG hf' hf
     obtain ⟨hW,hFx⟩:= reimburses Z (fun _=>d) hN T₀ (le_refl b) hf (fun i hi h => pillar _ _ _ _ hi h (hZ i hi h)) hqf he' le_rfl (ht.trans n.le_succ)
     refine ⟨hx,fun t=> hu _ t ?_⟩
     let W':= C.omega N p (fun U=>∏ i∈t.val,T₀ b i U); have he:= History.partition_eq C.path h.wilson N p b ((ht.trans n.le_succ).trans hN); rw [hFx]; apply (Aligned.paid_by_partition h _ hW ((ht.trans n.le_succ).trans hN) _ ((continuous_finsetProd _ (fun i _=>swell_visit y s F T' S U hm hk w' Z F' i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).trans
     rw [he]
end YM.RG05Readout.Records
