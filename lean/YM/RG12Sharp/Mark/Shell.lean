import YM.UVExtension.Oasis.Flora
import YM.MergeProof.Beacon  -- use sendsCard, etc
/-!
# Strong ingress leakage: saw off all inherited **forced** addresses in MARK probe.

 Not reproving SAM portfolio. Key savings spotted in baseline `Graces.heavyK` proof: on gasKey article
 (old Loft.Forced NOT old Reg with sharp mask), Pond has no prince addresses, `sendsCard` input
 takes TRUE mass budget, but `Stampede/PaidAtom` requests and `heavyK` returns output in budget units
 of `mass / sqrt(fineForced)`. For our matrix purposes, need the much stronger r output of sendsCard;
 use its proof API before information erased in heavyK. Need also all histories f (not Wilson anchor).
 Works on Flora frames, comments cp29.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.RG12Sharp.Clamp
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open PhysicalNext PhysicalNext.Repeat
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Source MergeProof
open PhysicalNext.Repeat.Graces PhysicalNext.Repeat.Legato Bandage
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {h:G.Simple} {X : Metals G} {D:Rolls X.p} {A:Alloy X D} {R: Factor A} {l v:ℝ} {N m p d:ℕ}{Z:Bolt A} {Q: In A.B.a m p} {F: Labels.Frame G d}
local notation "H?"=> Issue.trail Z
local notation "i₀" => A.B.a.clock.J m
local notation "jn" => A.B.a.S.side (m+1) p
local notation "J" => A.B.a.S.side m p
local notation "B?" => A.B.a.clock.op m p
local notation "Π"=> A.B.a.budget m
local notation "Λ"=> D.L (A.B.a.clock.J (m+1))
local notation "Ρ"=> (H?).rep N p m
local notation "ϕ" => Labels.frames G
local notation "φ" => localSection G
-- specific feature
private lemma tin (h' : Nest R Z)(H : m<N) (U:Spring R N m p l v Q)(x:Set.Icc l v) (hc:(Issue.trail Z).rep N p m= U.result x.val) (he:(Issue.trail Z).rep N p (m+1)= Q x.val)
  {w K} (b:Bandage R K w) (hr: d ≤ A.B.a.clock.J m) (g:G.Simple)
  (i:ℕ)(f:Config G (A.B.a.S.side (m+1) p)→ℂ)(r:ℝ) (hf:f≠0) (ht:SlotFit (Q x) 0 i f)(hs:∀ U,‖f U‖ ≤ r): let a:= Doors.rate Λ *((Q x).p.mass ((Q x).activities.forced i).support r)
  ∃ P:Coefficient ((Labels.frames G).level d) J, Gig (φ d) (H?) N p m (hol G) (Extra.Histories.fare (Q x) i f) P 0 a a := by
    intro a; let L:= Λ; let Y:= Q x; let F':= Blush.fan (Q x) 0 i f r hs ht; have hv := support_zero (B?).ratio _ (show 0 ∈ F'.live.crest from ht.tagged hf); let H₀:= houseS U x; let m₀:= (Q x).p.mass F'.live.crest F'.live.weight; have hu:f≠0:=hf; let v':ℂ:= (L.val:ℂ)^d
    have hx: ∃ s:H₀.fragrances → ℝ, SumBudget (fun i=> Push.Local.reservedMass (Π) (locus F'.live H₀ 0 i) (s i)) (coinFee G (X.p.profile i₀) d L * m₀) ∧ ∀ i,prince F'.live H₀ i→ (Π).supBounds 0 (locus F'.live H₀ 0 i) (pane H₀ F' v' i) (s i):= by
         refine ⟨(fun _=>0),?_,fun i' he'=> (never H₀ F'.live i rfl i' he').elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) (F'.live.profit.trans ((Q x).p.loMass _ _ F'.live.profit)))
    have hV:= sendsCard g H h' b.r U x hc he b.clock b.stamp hr F' hv hx (show Doors.rate L * _ ≤ a from le_rfl)
    have hX : Local.Readable (hol G) (localSection G d) (Ρ).p J (authors A.B.a m) := by rw [(Z.choice.represents N p m H.le).vac]; exact livelyCard b.clock hr (n:=p)
    obtain ⟨S,hS,-,-⟩:= MergeProof.grow hV (Z.choice.represents N p m H.le) hX; have h : Extra.Histories.fare (Q x) i f = F'.milk:= Blush.rose (Q x) 0 i f r hs ht; exact ⟨S,h.symm ▸ hS⟩
-- pay ANY single atom, at MUCH tighter scale than declared Mood. Actor.Select support.
lemma shelf (h' : Nest R Z) (H : m<N) {w K} (b:Bandage R K w) (hr: d ≤ A.B.a.clock.J m) (g:G.Simple)
  (i:ℕ)(f:Config G (A.B.a.S.side (m+1) p)→ℂ)(r:ℝ) (ht:SlotFit ((Issue.trail Z).rep N p (m+1)) 0 i f)(hs:∀ U,‖f U‖ ≤ r): let Y:= (H?).rep N p (m+1); let a:= Doors.rate ((Issue.trail Z).S.block m) *(Y.p.mass (Y.activities.forced i).support r)
  ∃ P:Coefficient ((Labels.frames G).level d) J, Gig (φ d) (H?) N p m (hol G) (Extra.Histories.fare Y i f) P 0 a a := by
   obtain ⟨l,v,Q,hT,x,hx,hQ,hz⟩:= (h'.held N m p H).1; let x':Set.Icc l v :=⟨x,hx⟩
   have hb : (Issue.trail Z).rep N p m=hT.result x':=hz; have hx':(Issue.trail Z).rep N p (m+1)=Q x':=hQ; intro Y a; by_cases hf:f=0; swap
   · unfold a; rw [show (Issue.trail Z).S.block m=Λ from PriceCompiler.block_eq A.B.valid _,show Y= Q x' from hx']; exact tin h' H hT x' hb hx' b hr g i f r hf (hx' ▸ ht) hs
   have hh:0≤a:=mul_nonneg (Doors.rate_pos _|>.le) (mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hs 1)))
   let q:= duet (Issue.trail Z) N p m hb hx' (sandboxK hT x')
   have hz:Extra.Histories.fare Y i f=0:=funext fun U=>by rw [Extra.Histories.fare, show f U=0 from congr_fun hf U,zero_mul,mul_zero]; rfl
   obtain ⟨P,hP,-⟩:= MergeProof.zeroSlot (localSection G d) (Issue.trail Z) N p m (hol G) (fun _=> True) q Z.choice hh hh; rw [hz]; exact ⟨P,hP⟩
section golfer
variable (B:SectionData F)(H:History G)(T:Coefficient F (H.S.side (m+1) p))
local notation "Ψ"=> H.rep N p (m+1)
open Extra.Histories
-- actual contribution, fully dynamical gas
-- redeclare binders in def
def inheritance {G:Gauge} {d:ℕ}{F:Labels.Frame G d}{n:Side}(R:Rep G n)(T:Coefficient F n) (U:Config G n):ℂ:= (Real.exp (R.exponent U):ℂ) * ∑' i,T.marked R i U
local notation "Y"=> inheritance (Ψ) T
lemma golfs (P:Hol G) (b:ℝ) (hV:H.Selected) (hm:m<N) (ht:T.Format 0 P (Ψ)) (hv:T.remBound 0 (Ψ) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) b) :
    let F' := fun i => Extra.Histories.fare (Ψ) i (T.forced i)
    Dominated F' ∧ (∀ i,Measurable (F' i)) ∧ Y=fun U=>∑' i,F' i U:=by
   intro F'; have hf:= hV.represents N p (m+1) hm; let P':= (Ψ); have hs:= dress_abs hf.good (rem_dominated hv)
   have hg: Envelope (fun x=> Real.exp (P'.exponent x)):= P'.exponentEnv hf.good|>.exp
   refine ⟨?_,fun i=> (Complex.continuous_ofReal.measurable.comp hg.meas).mul ((ht.borel i).mul (dressed_meas hf.good i)),?_⟩
   · obtain ⟨c,hc,h⟩:= hs; refine ⟨_,hc.mul_left hg.cost.choose,fun i U=>?_⟩; unfold F' Extra.Histories.fare; rw [norm_mul]; have hh:‖(Real.exp (P'.exponent U) : ℂ)‖ ≤ hg.cost.choose:= (Complex.norm_real _).trans_le (hg.cost.choose_spec _); exact mul_le_mul hh (h i U) (norm_nonneg _) ((norm_nonneg _).trans hh)
   funext U; unfold inheritance F' Extra.Histories.fare; rw [tsum_mul_left, dress_eq hf.good (rem_dominated hv)]
-- *explicitly* Σ of TRUE forcing addressed representations, different supports. when integrating each, same $coarse estimator.
lemma golf (P:Hol G) (b:ℝ) (hV:H.Selected) (hm:m<N) (ht:T.Format 0 P (Ψ)) (hv:T.remBound 0 (Ψ) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) b)
    (he:∀ (i:ℕ)(r:ℝ), (∀ U,‖T.forced i U‖ ≤ r) → let a:= Doors.rate (H.S.block m) *((Ψ).p.mass ((Ψ).activities.forced i).support r); ∃ P':Coefficient F (H.S.side m p),Gig B H N p m P (Extra.Histories.fare (Ψ) i (T.forced i)) P' 0 a a):let a:= Doors.rate (H.S.block m)*Real.sqrt (H.levels.clock.forcedAllowance (m+1))*b
   ∃ P':Coefficient F (H.S.side m p),Gig B H N p m P Y P' 0 a a:= by
    intro a; obtain ⟨ha,hb,hc⟩:= golfs H T P b hV hm ht hv; obtain ⟨r,s,h',_,hθ,_,_,e,hκ,hL⟩:=hv; choose X hX using fun i=> he i (e i) (hL i).2
    let v:= Doors.rate (H.S.block m); let u:= fun i=> v* (Ψ).p.mass ((Ψ).activities.forced i).support (e i); have hx: Summable u:= hκ.2.1.mul_left _
    have hz:= Gig.all_in B H N p m P hV hm.le (v:=(fun _=>0)) hX ha hb (by simp [Frame.coeffSize]) hx hx; have hM:(∑' i,u i) ≤ a:=by
        simp_rw [u,tsum_mul_left]; refine (mul_le_mul_of_nonneg_left hκ.2.2 (Doors.rate_pos (H.S.block m)|>.le)).trans ?_; rw [show a=v*(Real.sqrt (H.levels.clock.forcedAllowance (m+1))*b) from mul_assoc ..]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left h').trans hθ) (Real.sqrt_nonneg _)) (Doors.rate_pos _|>.le)
    beta_reduce at hc; rw [← hc,tsum_zero] at hz; exact ⟨_, hz.weaken hM hM⟩
end golfer
private def Aisle (H:History G) (V:Hol G) (B:SectionData F) (N p m:ℕ): Prop:= ∀(T: Coefficient F (H.S.side (m+1) p))(b:ℝ), T.Format 0 V (H.rep N p (m+1))→ T.remBound 0 (H.rep N p (m+1)) (Real.sqrt (H.levels.clock.forcedAllowance (m+1))) b→let a:= Doors.rate (H.S.block m)*Real.sqrt (H.levels.clock.forcedAllowance (m+1))*b; ∃ P:Coefficient F (H.S.side m p),Gig B H N p m V (inheritance (H.rep N p (m+1)) T) P 0 a a
lemma broad (h' : Nest R Z) (H : m<N) {w K} (b:Bandage R K w) (hr: d ≤ A.B.a.clock.J m) (g:G.Simple): Aisle (H?) (hol G) (φ d) N p m:=by
    intro T d' ht hv; exact golf _ _ T _ d' Z.choice H ht hv fun i r hh=>shelf h' H b hr g i _ r ⟨ht.invariant i,ht.borel i,ht.supported i,ht.carried i,ht.forcing i⟩ hh
/-- Any genuine weighted-marked coefficient at ANY fixed horizon, all periods/cutoffs.
  Requires same SETTINGS, Masks threshold R.p, physical witness Floral. output includes exact `Gig` on this `S.frame` Ra.
  When estimating consider `Gig.agrees`, `Gig.bound` remBound and orbit inequality etc. Doesn't assert Port.Force proof needed for any mask/measure projection under independently chosen histories.
-/
theorem recorded (C:Family G) (g:G.Simple) (he:UVExtension.Oasis.Floral (hG:=g) C) (hd:d ≤ C.path.levels.clock.J m) (hn:m<N) (T:Coefficient (C.labels.level d) (C.S.side (m+1) p)) (b:ℝ) (ht:T.Format 0 C.params (C.path.rep N p (m+1))) (hv:T.remBound 0 (C.path.rep N p (m+1)) (Real.sqrt (C.path.levels.clock.forcedAllowance (m+1))) b):
   let a:= Doors.rate (C.S.block m)*Real.sqrt (C.path.levels.clock.forcedAllowance (m+1))*b; ∃ P, Gig (C.localSection d) C.path N p m C.params (inheritance (C.path.rep N p (m+1)) T) P 0 a a:=by
   obtain ⟨M,P,A,R,S,Y,t,K,w,b',L,_,rfl,_,⟨h,hch⟩,_⟩:= he; exact broad hch.nest hn b' hd g T b ht hv
end YM.RG12Sharp.Clamp
