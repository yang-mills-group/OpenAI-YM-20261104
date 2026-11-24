import YM.RG05Readout.Many.Morrow
/-!
# This trajectory's exact m reopening

Costs from complete labelled proof `session` in smaller Census;
for actual joints keep specialized exact tests. Can demand only that any newly
used interaction vanishes on the admission map (not portal estimates
outside it). Then really continue in the full polynomial, with profiles
of all tuned one-mark letters. They were constant on root interactions by
evaluation inside m test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {j b k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "Y"=> C.path.rep N p
local notation "L!"=> C.path.levels.clock.op
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "λ₁"=> far C.path.levels
variable (A:Planner C p n V W) {H H':∀ i:ℕ,Census (V i)} (s:W→ℕ)(I:∀ i:ℕ,V i→ Body)
local notation "Λ"=>A.labelY
local notation "Φ"=>A.narrows
local notation "r₀"=>A.supportX
variable {F:∀ i:ℕ, Config G (C.side i p)→Poly (H i)} {F':∀ i:ℕ, Config G (C.side i p)→Poly (H' i)} (h:C.Makes) (L:OPE.Package C w r D) (hw:Storage C D)
variable {v:(i:W)→ℕ→Palette C (s i)} {T:Pens C p W} {f q:ℕ→ℝ}{B:ℕ→ℕ→ℝ}
local notation "w₀"=> west C q f k
local notation "λ₀"=> fun i:V N=>stepUp (A.motion (Λ N i)) (r₀ N i) (entrance C (s (Λ N i)) N p (v (Λ N i) N) 0 (I N i))
noncomputable def shadow (i:ℕ):Set (V i):={x|Cap (s (Λ i x)+2) (I i x) 0}
local notation "ι"=> shadow A s I
local notation "M"=> fun i=> if i=N then (t₁ i).supportExponent-4 else (t₁ i).supportExponent
omit [∀ i,DecidableEq (V i)] [∀ i,Fintype (V i)] in
lemma spilled (hk:n≤b)(hp:PreparedA A I b m hk) {i:ℕ}(j:V (i+1)) (hv:b≤ i)(ht:i < m) (hh:(Φ i (hk.trans hv) j).1∈ι i):j∈ι (i+1):=by -- {i} reorder
    unfold shadow; simp only [Set.mem_setOf_eq]; rw [hp i hv ht j,A.loyal i (hk.trans hv)]
    have hx: 1≤ ((C.S.block i).val:ℝ):=by exact_mod_cast (C.S.block i).property
    apply cap_aff _ (by positivity) (inv_le_one_of_one_le₀ hx) (Address.dist_box ..) hh
-- launched.top equality ℓ.C
omit [∀ i,DecidableEq (V i)] [∀ i,Fintype (V i)] in
lemma muted_atom (i:V N) (hp:i∈ι N): λ₀ i=0:=by
   dsimp only; rw [unlit C N p _ _ hp]; exact funext fun _=> scalar_z _
include h
lemma seen_top : Integrable (birth (H N) (Y N) λ₀) (prior G _):=by
   have he(i): Continuous (λ₀ i) :=by
      unfold stepUp; let Z:=Λ N i; let u:=v Z N; let f:= entrance C (s Z) N p u 0 (I N i)
      have hv: Continuous f:=by
          change Continuous (fun U=> f U); unfold f entrance; simp_rw [Finset.sum_apply]; exact continuous_finsetSum _ (fun j _=> ((((C.localSection _).continuous_places _ _).const_smul _).const_smul _))
      dsimp only; unfold Motion.scalar;split; exact ((hv.comp (continuous_pull ..)).star); exact hv.comp (continuous_pull ..)
   exact ((hatCont C N p (λ₀) he (show Continuous ((Y N).eval) by rw [(h.wilson.starts ..).2]; exact bare_cont _) (H N)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
variable {b j:ℕ}
omit [∀ i,DecidableEq (V i)] [∀ i,Fintype (V i)] in
lemma Lesson.cold (hb:b≤ N) (hp: Lesson (D:=D) h s j N N p T B q v) (he:j≤b)(i:V b)(hh:i∈ι b): imprint h A I T b hb i=0:=by
    let a:= Λ b i; obtain ⟨U,S,hU,ht,hK,hQ⟩:= hp.billing a
    unfold imprint; rw [ht]; obtain ⟨z,hV⟩:=(hU.legal b he hb).capacity0 (v a b)
    rw [show (U b (v a b)) (I b i)=0 from dormant hV hh]; exact spin_zero .. -- rw ht inference
omit h in
lemma Purse.slice (hp:Purse C f q n N d k)(hc:n≤b) (hd:m≤N): Purse C f q b m d k:=⟨fun i hi he=> hp.headV i (hc.trans hi) (he.trans hd),fun i hi he=>hp.nextV i (hc.trans hi) (he.trans_le hd),fun i hi he=>hp.upper i (hc.trans hi) (he.trans hd),fun i hi he=> hp.control i (hc.trans hi) (he.trans_le hd)⟩
-- need Lesson.from allows hr at b start. Spine restricting
lemma Lesson.revise (ht:Lesson (D:=D) h s j N N p T B q v)(hi:j≤ m)(hp:b≤N): Lesson (D:=D) h s m b N p T B q v:=by
   refine ⟨fun i=>?_⟩; obtain ⟨U,S,hU,hT,hΦ,hY⟩:=ht.billing i
   exact ⟨U,S,⟨hU.starts,fun i hv=> hU.legal i (hi.trans hv),fun i hv=>hU.follows i (hi.trans hv)⟩,hT, fun i ha hv=>hΦ i (hi.trans ha) (hv.trans_le hp),fun i ha hv=> hY i (hi.trans ha) (hv.trans hp)⟩
local notation "o!"=> apron C.path.levels
include hw L
lemma regenerate (hj:j≤b)(hp:n≤j)(hu:b ≤ N)(he:Purse C f q j N d k) (hl:Lesson (D:=D) h s j N N p T B q v)
    (ht:∀ i≤ d,C.ref i≤N)(hS:∀ i,s i≤ d)
    (hW:∀ i:V j, Cap (s (Λ j i)+2) (I j i) 1)(hP:PreparedA A I j N hp)
    (hY:F N=birth (H N) (Y N) λ₀)(hY':F' N=birth (H' N) (Y N) λ₀)(hx:∀ i≤ d,pricesTop ζ λ₁ N i ≤ (λ₁ N)*((C.path.levels.clock.hatBeta N)^k))
    (hO:Occupancy (r₀ N) (o! N))(hg:Toured A H (hp.trans hj) N f k)(hr:Replay A s (H:=H) (hp.trans hj) N F N) (hr':Replay A s (H:=H') hp N F' N)
    (hC:∀ i:ℕ, b ≤ i → (H i).choices⊆(H' i).choices) (hG:∀ i:(H' b).Mode,i.val∉ (H b).choices → ¬Disjoint (ι b) (i.val:Set (V b))) :
     MenuBoard (R:=H' b) (Y b) (imprint h A I T b hu) (F' b) (r₀ b) (fun _:V b=>w₀ b) (M b) 1 :=by

   have hp' := cap_lives A s I hp hj hu hP hW
   have h' : PreparedA A I b N (hp.trans hj):= fun i hi h=> hP i (hj.trans hi) h
   have hB:= assemble A s I h L hw (hp.trans hj) hu (he.slice hj (N:=N) (m:=N) le_rfl) (hl.revise s h hj (b:=N) le_rfl) ht hS hp' h' hY hx hO hg hr b le_rfl hu
   have hv : Integrable (F N) (prior G _):=by rw [hY]; exact seen_top A s I h
   have hv' : Integrable (F' N) (prior G _):=by rw [hY']; exact seen_top A s I h
   have hi(U p):¬Disjoint (ι b) (p.val:Set (V b))→(F b U).part p=0 :=hr.black _ s (ι) _ hu hv le_rfl (fun i h hm x=>spilled A s I hp hP x (hj.trans h) hm) (fun U p h' => by rw [hY]; exact birth_dark (ι N) (muted_atom A s I) _ _ h') le_rfl hu _ _
   have hi'(U p):¬Disjoint (ι b) (p.val:Set (V b))→(F' b U).part p=0:=hr'.black _ s ι hp (hj.trans hu) hv' le_rfl (fun i h hm x=>spilled A s I _ hP x h hm) (fun U p h'=> by rw [hY']; exact birth_dark (ι N) (muted_atom A s I) _ _ h') hj hu _ _
   -- build relation before separating; opening at b. Need preserve integrability etc.
   have hQ:F' b= fun U=>wrap (H b) (H' b) (F b U):=by
       funext U; ext i; by_cases hz:i.val∈ (H b).choices
       · let a:(H b).Mode:=⟨_,hz⟩; have hQ := hr.narrowing A s _ hp hj hr' hC hu hv' le_rfl (fun U=> by rw [hY,hY']; exact (birth_choice _ _ (hC N hu) U).symm) (i:=b) le_rfl hu U
         rw [show i=route (hC b le_rfl) a from rfl,wrap_right,hQ,narrow_right]
       rw [wrap_off _ i hz]; exact hi' U i (hG i hz)
   have hxw:∀ i∈ι b,let f:=imprint h A I T b hu i; f.2.1=0 ∧ profile (Y b).activities f.2.2=0:=by
      intro i Hz f; unfold f; rw [hl.cold A s I h hu hj i Hz]; refine ⟨rfl,?_⟩; ext; simp [profile,cram] -- replace
   refine ⟨hr'.live A s hp hv' le_rfl hj hu,hB.fettled,?_⟩
   rw [hQ]; apply open_served (hC b le_rfl) (ι b) hxw (fun _=>mul_pos (he.upper b hj hu).1 (grantw (he.headV b hj hu))) hB.grants hi hG
end YM.RG05Readout.Many
