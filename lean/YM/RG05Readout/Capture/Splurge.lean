import YM.RG05Readout.Capture.Traces
/-!
# Culmination of capture from the upper height

On full physical transcript in actual Family. At mesh n, after opening at m,
transmit term all the way and fold occupancy. Produce explicit Tsch-price and
keep all counter K receipts through replay adjustment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{W:Type}[DecidableEq W][Fintype W]
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {k l g:ℕ}
set_option quotPrecheck false
local notation "S0"=> C.path.levels
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "X"=> C.path
local notation "Ζ"=> C.path.levels.budget
local notation "u"=> Legato.Bandage.renal C.path.levels
local notation "p0"=> C.path.levels.budget n
local notation "L!"=> C.path.levels.clock.op
local notation "L₁"=> C.S.block n
local notation "ℓ"=> Copper.ld C.path.levels n
variable (o:W→Site (C.side n p)) (E:W→Motion) (s:W→ℕ) (I:∀ i:ℕ,ManyStem C o i→Body)
local notation "V'"=> ManyStem C o
local notation "A'"=> Mine.tree o E
local notation "Λ"=>(A').labelY
local notation "Φ"=>(A').narrows
local notation "H!"=> Mine.ward o E
local notation "r₀"=>(A').supportX
local notation "π"=>fun c:V' n => (A').motion ((A').labelY n c)
variable (h:C.Makes) (L:OPE.Package C w r D) (hw:Storage C D) (heC:Cater C D)
variable {f q:ℕ→ℝ}{B:ℕ→ℕ→ℝ}{Q:ℝ} {Λ':Census W} {F:∀ i:ℕ, Config G (C.side i p)→Poly (Mine.ward o E Λ' i)}

variable (P:(i:W)→ Sight C (s i) p) (S:(i:W)→Emblems C (s i)) (x:(i:W)→Palette C (s i))
local notation "v"=> Launch (m:=m) s S x
local notation "T!"=> plants (m:=m) s P S x
local notation "λ₀"=> fun i : V' N=>stepUp ((A').motion (Λ N i)) (r₀ N i) (entrance C (s (Λ N i)) N p (v (Λ N i) N) 0 (I N i))
local notation "Y!"=> fun i=> if i=m then (Ζ i).supportExponent-4 else (Ζ i).supportExponent
local notation "Z0"=> apron C.path.levels

noncomputable def crust (C:Family G)(m n d k:ℕ)(Q:ℝ):ℝ := min (1/2) (Legato.Bandage.renal C.path.levels n * envelope C m (d+1) k Q (n+1) * ((C.S.block n).val:ℝ)⁻¹ ^ (4+d)) -- L shrinks.stake+1/2
local notation "Φ₀"=> crust C m n d k Q

noncomputable def baseFold (R:Census W)(U: Poly (Mine.ward o E R n)) := feed (fun _=> 1) (chamber R ((A').labelY n)) U
-- Mint End
open Ribbons
local notation "ζ"=> Many.envelope C m (d+1) k Q (n+1)
structure Furls (T:Levels G) (i:ℕ)(t:ℝ): Prop where
    eye : let δ:= renal T i; let l:= T.budget i; let B:= l.B; 0 ≤ t ∧ 0<δ∧ δ ≤ 1 ∧100 ≤ l.supportExponent ∧
        ((B+B+1:ℕ):ℝ)^4*(t + apron T i*siteFactor B*δ)≤1/2∧ let p:=MergeProof.Ribbons.scurry T (apron T) (fun _=>t) δ i; ((B+B+1:ℕ):ℝ)^4*p ≤1/2 ∧ Real.exp p-1 ≤ 1
include h hw L heC
local notation "Δ"=> (L! n p)
local notation "U"=> Address.Bud C p n
local notation "Λ'!"=> (Φ n (le_refl n))
set_option maxHeartbeats 750000 in
lemma panorama (H:∀ i:W,Spine D B h n p (s i) N (P i) (S i)) (hk:n < m)(hm:m ≤ N)(ho:Occupancy o ((K).J n))
    (hc:Clearance o E s I Λ' m) (hp:PreparedA A' I n N le_rfl) (hQ:∀ j: V' n, Cap (s (Λ n j)+2) (I n j) 1)
    (hX:∀ i:W,size (x i) ≤ Q) (hy:0 < Q)
    (ht:Warm C n (d+1) k) (hS:∀ i:W,s i ≤ d)
    (hF:F N=birth (Mine.ward o E Λ' N) (Y N) λ₀) (hr:Replay A' s (H:=H! Λ') (le_refl n) N F N):
    let qt i:= baseFold o E Λ' (F n i)
    0< Φ₀ ∧ Integrable qt (prior G (C.side n p)) ∧ ∃ (t:ℝ), Furls S0 n t ∧ Alcove (Y n) ((imprint h A' I T! n (hk.trans_le hm).le) ∘ (Mine.remap o E).symm) qt o (fun _=> Φ₀) t (u n) (1/2):=by
    intro z; let T:=total C Q (d+1) m
    have hn: n<N:= hk.trans_le hm
    obtain ⟨a,b,hC,hG,hA⟩:= heC.tiers n N p hn
    obtain ⟨χ,hY⟩:=hr.downhill (V:=V') n (le_refl n) hn
    let f:= Λ'!; let g:= Prod.fst ∘ f
    have he : 0 < ζ:=mul_pos (rust_paid _).1 (grantw (totalpos hy _)); let s₀:= (p0).supportExponent; let t:= u n; let a:=(L₁).val; let c:=t*ζ; let M:=(a:ℝ) ^ d; let Z₁:= Φ₀; have hw:0 < t:= hC.poses.hats.1
    have hL:1 ≤ (a:ℝ):=by exact_mod_cast (C.S.block n).property
    have hw' : 0< Z₁:=lt_min (by norm_num) (mul_pos (mul_pos hw he) (by positivity));
    have ho':= Mine.pays o E (le_refl n) ho (le_refl _)
    have hx:= docks o E s I h L (show Storage C D from ‹_›) P S x H hk.le hm ho hc hp hQ hX hy ht hS hF hr (n+1) n.le_succ hk
    have hL' : Lesson (D:=D) h s n N N p T! B T (Launch (m:=m) s S x):= ⟨fun i=> ⟨P i,S i,H i,fun _=>rfl,fun j _ _=> nearpoints ..,fun j hj hv=> head_cost (H i) hk.le hm (Nat.add_le_add_right (hS i) 1) (hX i) hj hv⟩⟩ -- match
    let x' j:= ℓ*(ℓ*T n)*j; let q:=fun i:V' (n+1)=> budwgt C p n (s (Λ n (g i)))
    have hP(i: V' n):Train (D N p n hn) (keys0 h hn) (d:=s (Λ n i)) (T! (Λ n i) (n+1)) (T! (Λ n i) n) (ℓ*(ℓ*T n)):= (hL'.lights s h).brings n le_rfl hn hn (Λ n i)
    have hV(i: V' (n+1)): Signpost (Y (n+1)) (π (g i)) (r₀ (n+1) i) ((T! (Λ n (g i)) (n+1)) (headFee C p n (f i).2 (I n (g i)))) (imprint h A' I T! _ hn i):=by
       have ht': Λ (n+1) i=Λ n (g i):= (A').loyal ..; dsimp only at * -- likely changes if predicates notation; avoid!
       rw [← show I (n+1) i= headFee C p n (f i).2 (I n (g i)) from hp n le_rfl hn i, ← ht']
       exact View.spin_at ..
    have hZ: Alcove (R:= H! Λ' n) (Y n) (imprint h A' I T! n hn.le) (F n) (r₀ n) (fun _=> Z₁) b t (1/2) :=by
       let W:=fun i:V' n=> T! (Λ n i) (n+1); rw [hY]; apply budholds (ν:=f) (T:=W) (s:=s ∘ Λ n) (S:=fun i=> T! (Λ n i) n) h hC (wheel h A' n hn.le) hn hP hx _ ho'.1 ho'.2 ((A').future n le_rfl) χ hV hQ (fun _=>he) _ (fun _=>hw') _
       ·
         dsimp only; split; rfl; linarith only
       · intro i; let u':=rusty C m k (n+1)
         have hE : T n ≤ ((L₁).val:ℝ)^(d+1)* T (n+1):=(totalclose (C:=C) (Q:=Q) (d:=d+1) hk).le
         exact (ht.bears n le_rfl).2.first _ _ u' (totalpos hy _) (totalpos hy _) (rust_paid _).2 (rust_paid _).1 hE
       intro i; change Z₁*‖q i‖ ≤ c/_; rw [show (Fintype.card U)= (C.S.block n).val^4 from site_card _,Nat.cast_pow]; have h_M:‖q i‖≤ M:= (bud_price _).trans (pow_le_pow_right₀ hL (hS _)); change Z₁*_ ≤ c/(a:ℝ)^4; apply (mul_le_mul_of_nonneg_left h_M hw'.le).trans
       apply (mul_le_mul_of_nonneg_right (show Z₁≤ c*((a:ℝ)⁻¹)^(4+d) from min_le_right ..) (show 0≤M from by unfold M; positivity)).trans_eq; unfold M; have hα: (a:ℝ) ≠ 0:=by positivity
       rw [pow_add,inv_pow,inv_pow,mul_assoc c,mul_assoc ((↑a:ℝ)^4)⁻¹, inv_mul_cancel₀ (pow_ne_zero d hα), mul_one, div_eq_mul_inv]
    have hB' : Integrable (F n) (prior G _):=by rw [hY]; exact feed_live _ _ (StepData.push_integrable (C.path.levels.transition_mass ..) _ hx.cleared)
    have hb:0 ≤ b:=by obtain ⟨_,_,_,_,_,hX,-⟩:=hZ.chamber; obtain ⟨f,_,h,-⟩:= hX; exact (tsum_nonneg ((h 0).1)).trans (h 0).2.2
    exact ⟨hw',feed_live _ _ hB',b,⟨hb,hC.poses.hats.1,hC.poses.hats.2,hC.poses.exp.1,hC.poses.stakes.1,hG,hA⟩,Alcove.squeeze o E h hn.le hZ hB' hw' hw.le (by norm_num)⟩
end YM.RG05Readout.Many
