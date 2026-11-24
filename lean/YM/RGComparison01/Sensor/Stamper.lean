import YM.RGComparison01.Post.Split
import YM.RGComparison01.Fiber
import YM.RGComparison01.Turnstile
/-! # Pad with infinitely many rooted copies of a fixed neighbourhood
 on EVERY period. Preserve full gas, footprints and authentic cost in old
 Ω column (no claim old ≡ small coupling). Allows room for injecting tests
 locally before marker estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{n N:Side} {A:Activities G n}
    (R:RG.Rep G n) (r:ℕ)
open Post.Split
abbrev dim (A:Activities G n):Activities G n:= {A with E:=0}
abbrev pad (A:Activities G n):Activities G n:= hub (dim A) A A
abbrev stand : RG.Rep G n:= {R with activities:=pad R.activities}
def rod (x:Site n)(k:ℕ):ℕ:= (Post.Split.tie n).symm (.inr (.inr (k,(1,x),⟨neighbors r 0, (neighbors_mem ..).2 (by rw [separation_self]; exact Nat.zero_le _)⟩)))
local notation "u"=> pad A
lemma rods (x:Site n)(k:ℕ): ((pad A).reg (rod r x k)).site=x ∧ ((pad A).reg (rod r x k)).support=neighbors r x∧ (pad A).E (rod r x k)=0:= by
    unfold pad hub rod; simp only [Function.comp_apply, Equiv.apply_symm_apply]; refine ⟨rfl,?_,rfl⟩
    have hv:= PhysicalNext.Repeat.Turn.circle_wind 1 x 0 r
    rw [Lattice.affine,Signed.act_zero,zero_add] at hv; exact hv.symm
lemma rods_inj: Injective fun p:Site n ×ℕ=> rod r p.1 p.2:=by
   intro i j h
   let f (z: Site n ×ℕ): Parts n:= Post.Split.tie n (rod r z.1 z.2); have hh:f i=f j:=congr_arg (Post.Split.tie n) h
   simp only [f,rod,Equiv.apply_symm_apply,Sum.inr.injEq,Prod.mk.injEq] at hh; exact Prod.ext hh.2.1.2 hh.1
abbrev rode (_A:Activities G n) := Equiv.ofInjective (fun p:Site n ×ℕ=> rod r p.1 p.2) (rods_inj r)
-- avoids shadow keep equality at probes
abbrev stance (r:ℕ) : Ribbon (stand R) r:=by
   let f (i:ℕ):= i∈ (Set.range fun p:Site n × ℕ=> rod r p.1 p.2); let B:= rode r R.activities
   refine ⟨f,(fun i=> (B.symm i).2),fun j=> ?_,fun i hi=> ?_⟩
   · let s:Finset (Site n×ℕ):= Finset.univ ×ˢ (Finset.range (j+1)); refine ((s.finite_toSet).image B).subset (fun i hi=>?_) -- univ type
     exact ⟨B.symm i,Finset.mem_product.mpr ⟨mem_univ _, Finset.mem_range.mpr (Nat.lt_succ_of_le hi)⟩, B.apply_symm_apply _⟩
   obtain ⟨a,rfl⟩:=hi; obtain ⟨h,h',-⟩:= rods (A:=R.activities) r a.1 a.2; rw [show ((stand R).activities.reg _).support= neighbors r _ from h',show ((stand R).activities.reg _).site =_ from h]
abbrev tag := rode r R.activities
set_option quotPrecheck false
local notation "Γ"=> stance R r
local notation "K"=> (pad R.activities)
local notation "x"=> (tag R r)
lemma rideZ (p:Site n×ℕ) : (Γ).ride (x p)=p.2 :=by change ((x).symm (x p)).2=p.2; rw [Equiv.symm_apply_apply]
lemma man (p:Site n×ℕ) : (Γ).home (x p)= p.1∧ (((stand R).activities.reg ((x p).val)).support)=neighbors r p.1∧ (K).E (x p).val=0:= rods r p.1 p.2
local notation "m"=>mystery n
lemma sighted : Drawing.Opens (stance R r) (mystery n):= by
    refine ⟨?_,?_⟩
    · rintro i ⟨a,ha⟩ ⟨v,hv⟩
      unfold rod at hv; subst i; simp at ha
    intro i hi he U
    have hp : (pad R.activities).E i=0:= by change songs _ _ (Post.Split.tie _ i)=0; rcases ht: Post.Split.tie n i with j|j|j ; rfl; exact (hi ⟨_,ht⟩).elim; rfl -- split_ifs? remove
    unfold Activities.regularOccurrence; rw [show (stand R).activities.E i=0 from hp]; simp [RG.masked]
local notation "P'"=> R.p
variable (p: BudgetPoint)
lemma dims_B (A:Activities G n) : (dim A).EBound p 0 := by
    refine ⟨fun _=>0,fun i=> ?_,fun i=>?_⟩
    · exact CouplingShape.sup_larger (CouplingShape.sup_const 0) abs_zero.le
    simp [SumBudget,BudgetPoint.mass]
lemma dims_A (A:Activities G n) : (dim A).RegularFamily p:=by
    refine ⟨fun i=> CouplingShape.reg_const 0,fun i=>rfl,fun i h X Y _ _=>?_⟩
    unfold logHessian; change iteratedFDeriv ℝ 2 (fun _ :Directions G n=> (0:ℝ)) 0 _=0; simp
lemma dims_J {s:Signed}{b:Site n}(h : Nonempty (A.Moves s b)): Nonempty ((dim A).Moves s b):= by
    obtain ⟨t⟩:=h; exact ⟨⟨t.ep,t.kp,t.reg_site,t.reg_support,t.forced_support,t.forced_inventory,t.forced_tests,fun _ _=>rfl,t.valuesK⟩⟩
variable {w d:ℝ}
lemma lights {B:BudgetPoint} (h:A.Valid B d w): (pad A).Valid B d w:=by
    simpa only [zero_add] using! Post.Split.still (dims_A B A) h.regular (fun s b=> dims_J (h.moves ..)) h.moves (dims_B B A) h.boundE h
lemma valid {q:BudgetPoint} (h : R.activities.Valid q w d) : (stand R).activities.Valid q w d := lights h
lemma day (h:R.activities.EBound R.p w) : (stand R).eval=R.eval:=by
    have hp:=dims_B R.p R.activities
    have ht (V:Config G n): (pad R.activities).additive R.p V=R.activities.additive R.p V:= Post.Split.consumes («Z»:=R.activities) (D:=R.activities) (C:=dim R.activities) rfl rfl (by rw [show (dim R.activities).E=0 from rfl, zero_add]) hp h V
    funext v; apply congr_arg₂ _ (congr_arg Real.exp ?_) rfl
    unfold RG.Rep.exponent; simp only [ht]
lemma mask_B (h:R.activities.EBound R.p d): (Tithe.portion (stand R).activities (mystery n)).EBound R.p d:= tidy h _ _
variable {J:ℕ} (S:RG.Rep G N) (hN:N.val=n.val*J)
local notation "Φ"=> stance S r
local notation "θ"=> tag S r
local notation "y" => (Deck.divides hN)
local notation "C'"=> (Macrame.splitter (Deck.divides hN))
def castP : (Φ).Node→ (Γ).Node:= fun i=> x (C' ((θ).symm i).1, ((θ).symm i).2)
-- tag lists total, account passenger direction later
local notation "L"=> castP R r S hN
lemma billed (i:Site N×ℕ): castP R r S hN (θ i)= x (C' i.1,i.2):= by unfold castP; simp
lemma neigh_f (i : Site N): (neighbors r i).image (C')= neighbors r (C' i):= by
    ext j; constructor
    · rintro h; obtain ⟨k,hk,rfl⟩:= mem_image.mp h; exact (neighbors_mem ..).2 ((Deck.less (y) ..).trans ((neighbors_mem ..).1 hk))
    intro h; let k:= Deck.rise (y) i j; exact mem_image.mpr ⟨k,(neighbors_mem ..).2 ((Deck.climb ..).trans_le ((neighbors_mem ..).1 h)),Deck.dawns ..⟩
lemma crosses : Ribbon.Drops (stance R r) (stance S r) hN L:= by
    refine ⟨⟨(fun i=> ?_), (fun i j h'=> ?_), (fun i j he h'=> ?_)⟩,fun i=>?_,fun i=>?_,fun i V=>?_⟩
    · obtain ⟨v,rfl⟩:= (θ).surjective i; rw [billed,(man R r _).1,(man S r _).1]
    · obtain ⟨v,rfl⟩:= (x).surjective j; have ht := man R r v|>.1
      have hh : v.1=C' i:= ht.symm.trans h'; refine ⟨θ (i,v.2),?_,man S r _ |>.1⟩; rw [billed]; exact congr_arg _ (Prod.ext hh.symm rfl)
    · obtain ⟨a,rfl⟩:= (θ).surjective i; obtain ⟨b,rfl⟩:= (θ).surjective j
      simp only [billed] at he; have hh:= congr_arg Prod.snd ((x).injective he)
      exact congr_arg _ (Prod.ext ((man S r _).1.symm.trans (h'.trans ((man S r _).1))) hh)
    · obtain ⟨v,rfl⟩:= (θ).surjective i; rw [billed, rideZ,rideZ]
    · obtain ⟨v,rfl⟩:= (θ).surjective i; rw [billed,(man R r _).2.1,(man S r _).2.1]; exact (neigh_f r hN _).symm
    obtain ⟨v,rfl⟩:= (θ).surjective i
    rw [billed]; unfold Activities.regularOccurrence stand; dsimp only; rw [(man R r _).2.2,(man S r _).2.2]; simp [masked]
end YM.RGComparison01.Sensor
