import YM.RG05Readout.Many.Nodes
/-!
# Vertical choices with bans at a frontier

`Lift` purchases EXACT untruncation in fine variables for chosen sets in
coarse ring (and all singletons). Nested compositions on the same Census
using `old_hall`. Thus startups can retain the original bans then be
safely reconsidered at m.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
section
variable {V I W: Type*}[DecidableEq V][DecidableEq I][DecidableEq W][Fintype V][Fintype I]
variable {R:Census W}{ψ:I→W}{θ:V→I}
def Lift (R:Census W)(ψ:V→W): Census V where
   choices := Finset.univ.filter fun i => Lit R ψ i
   blank:= mem_filter.mpr ⟨Finset.mem_univ _,dark_empty⟩
   solo i:= mem_filter.mpr ⟨Finset.mem_univ _,dark_one i⟩
   down h _ hy:= mem_filter.mpr ⟨Finset.mem_univ _,Lit.down ((mem_filter.mp h).2) hy⟩ -- implicit x
lemma chamber (R:Census W)(ψ:V→W):License R (Lift R ψ) ψ:=fun _ h=> mem_filter.mpr ⟨Finset.mem_univ _,h⟩
omit [Fintype V] [DecidableEq V] in
lemma Lit.chain (s:Finset V) : Lit R (ψ ∘ θ) s ↔ Lit (Lift R ψ) θ s:=by
    constructor
    · rintro ⟨h,ht⟩; simp_rw [← Finset.image_image] at h
      refine ⟨mem_filter.mpr ⟨Finset.mem_univ _, ⟨h,?_⟩⟩,fun i hi j hj he=>ht hi hj (congr_arg ψ he)⟩
      intro i hi j hj he; obtain ⟨a,ha,rfl⟩:=mem_image.mp hi; obtain ⟨b,hb,rfl⟩:= mem_image.mp hj; exact congr_arg _ (ht ha hb he)
    rintro ⟨ht,h⟩; have he: Lit R ψ (s.image θ) :=(mem_filter.mp ht).2; exact ⟨by rw [← Finset.image_image]; exact he.1,fun i hi j hj hI=> h hi hj (he.2 (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hI)⟩
lemma Lift_nested (R:Census W)(ψ:I→W)(θ:V→I): (Lift R (ψ ∘ θ)).choices=(Lift (Lift R ψ) θ).choices:=by unfold Lift; ext; simp only[mem_filter,Finset.mem_univ,true_and]; exact Lit.chain _
lemma Lift_retrieve (R:Census W)(ψ:I→W)(θ:V→I):License (Lift R ψ) (Lift R (ψ ∘ θ)) θ:=fun i h=> by rw [Lift_nested]; exact chamber _ _ i h
lemma Lift_mono {R S:Census W}(h:R.choices⊆S.choices) (ψ:V→W) : (Lift R ψ).choices ⊆ (Lift S ψ).choices:=by
    intro i hi; have H: Lit R ψ i:=(mem_filter.mp hi).2; exact mem_filter.mpr ⟨Finset.mem_univ _,h H.1,H.2⟩
end
variable {G:Gauge} {C:Family G} {n m p N d:ℕ} {W:Type}[Fintype W] [DecidableEq W]
    {D:Address.Rail C} {w:Worth}{u:ℕ→ℕ} {j b k i:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "X"=> C.path
local notation "Y"=> C.path.rep N p
local notation "O"=> Address.Bud C p
local notation "λ₀"=> C.path.levels.clock.op
local notation "Θ"=>C.S.toDepth
local notation "pB"=> C.path.levels.budget

variable (x:W→Site (C.side n p))
local notation "R!"=>ManyStem C x
variable (r:W→Motion)
local notation "A"=> Mine.tree x r
namespace Mine
omit [DecidableEq W] [Fintype W] in
def shelter (hk:n ≤ b) (ht:b ≤ i) (j: ManyStem C x i): ManyStem C x b := ⟨(j.val.1,(Θ ht p).parent j.val.2),fun h=> by dsimp only; rw [← parent_nested (Θ h p) _ (Θ (hk.trans ht) p) (C.S.toDepth_odd h p) (C.S.toDepth_odd ht p)]; exact j.property (hk.trans ht)⟩
omit [DecidableEq W] [Fintype W] in
lemma spec_grow (hk:n ≤ b)(ht:b ≤ i)(j:ManyStem C x (i+1)): shelter x hk (ht.trans i.le_succ) j = shelter x hk ht ((tree x r|>.narrows i (hk.trans ht)) j).1:=by
    let l:= (tree x r).narrows i (hk.trans ht); let v:= l j
    let w:= v.1; let z:= grow x r (hk.trans ht) w v.2; have he:z=j:= l.symm_apply_apply _
    refine Subtype.ext (Prod.ext (show j.val.1=w.val.1 from (tree x r).loyal ..) ?_)
    change (Θ _ p).parent j.val.2= (Θ ht p).parent w.val.2; rw [parent_nested (Θ ht p) (λ₀ i p|>.ratio), ← show ((λ₀ i p).ratio).parent z.val.2 = w.val.2 from rootKeeps .., he]; exact C.S.toDepth_odd _ _; exact C.S.block_odd _
omit [DecidableEq W] [Fintype W] in
lemma vanishDepth (j:ManyStem C x b)(hk:n≤ b) : shelter x hk (le_refl _) j=j:=by
   let u:= (Θ (le_refl b) p); have he:u.count.val=1:= Nat.eq_of_mul_eq_mul_left (C.S.side b p).property (u.exact_size.symm.trans (Nat.mul_one _).symm)
   have ht : u.embed j.val.2=j.val.2:=by rw [Ratio.embed,he,one_smul,wrap_lift]
   exact Subtype.ext (Prod.ext rfl ((congr_arg u.parent ht.symm).trans (Ratio.embed_parent ..))) -- may infer

def ward (B:Census W)(i:ℕ): Census (R! i):= Lift B ((A).labelY i) -- r needed? used!
def masts (hk:n ≤ b) (B:Census (ManyStem C x b))(i:ℕ): Census (R! i):= if h:b ≤ i then Lift B (shelter x hk h) else (Lift (Stock.census W) ((A).labelY i)) -- Bud ambiguous; below arbitrary. use Skin BNorth
lemma wardlight (B:Census W)(hk:n ≤ i): License (ward x r B i) (ward x r B (i+1)) (Prod.fst ∘ (A).narrows i hk) :=by
    unfold ward; rw [show (A).labelY (i+1)= (A).labelY i ∘ (Prod.fst ∘ (A).narrows i hk) from funext fun j=>(A).loyal ..]; apply Lift_retrieve
lemma dawnwide (hk:n ≤ b) (B:Census (R! b))(hi:b ≤ i): License (masts x r hk B i) (masts x r hk B (i+1)) (Prod.fst ∘ (A).narrows i (hk.trans hi)):=by
    unfold masts; rw [dif_pos hi,dif_pos (hi.trans i.le_succ), show shelter x hk (hi.trans i.le_succ) = shelter x hk hi ∘ Prod.fst ∘ (A).narrows i (hk.trans hi) from funext fun j=> spec_grow x r hk hi j]; apply Lift_retrieve
lemma masts_le (hk:n ≤ b)(B':Census (R! b))(S:Census W) (he:B'.choices⊆(ward x r S b).choices)(hi:b≤ i): (masts x r hk B' i).choices⊆ (ward x r S i).choices:=by
    refine subset_trans (b:=(Lift (ward x r S b) (shelter x hk hi)).choices) ?_ ?_; rotate_left; show (Lift (ward x r S b) (shelter x hk hi)).choices⊆(ward x r S i).choices; unfold ward; rw [← Lift_nested]; apply Finset.Subset.refl _ -- defeq coe?
    unfold masts; rw [dif_pos hi]; exact Lift_mono he _

-- anchor coverage with Stock prices.Larger V universes unsupported by Drake pals but layout works.
lemma isolation (S:Stock.Tabs C.path.levels) {k i:ℕ}(hh:k ≤ i) (a b:Site (C.side i p))(he:(C.path.levels.budget k).B^2+1 ≤ separation ((Θ hh p).parent a) ((Θ hh p).parent b)) : (C.path.levels.budget i).B^2+1 ≤ separation a b:=by
    induction i,hh using Nat.le_induction with
    | base=>
       let P:=(Θ (le_refl k) p); have hv:P.count.val=1:= Nat.eq_of_mul_eq_mul_left (C.S.side k p).property (P.exact_size.symm.trans (Nat.mul_one _).symm)
       have ht(i):P.parent i=i:=by
           have he:P.embed i=i:=by rw [Ratio.embed,hv,one_smul,wrap_lift]
           exact (congr_arg P.parent he.symm).trans (Ratio.embed_parent ..)
       change _ ≤ separation (P.parent a) (P.parent b) at he; rw [ht,ht] at he; exact he
    | succ i hi ih=>
       let P:=(λ₀ i p).ratio; let K':=(pB i).B
       rw [parent_nested (Θ hi p) P _ (C.S.toDepth_odd hi p) (C.S.block_odd i), parent_nested (Θ hi p) P _ (C.S.toDepth_odd hi p) (C.S.block_odd i)] at he
       have hp:= Nat.mul_le_mul_left P.count.val (ih _ _ he); rw [mul_add,mul_one, ← both] at hp -- `Station` namespace
       have ht:= midway P (C.S.block_odd _) a; have hu:= midway P (C.S.block_odd _) b
       have hL:P.count.val ≥ 3:= C.S.block_large _
       -- cover grows ≤ 2 times squared so strict gain
       have hw:= Nat.mul_le_mul_right (K'^2) (by omega : 2 ≤ P.count.val); have hh := le_trans (a:=(pB (i+1)).B^2) (S.grows i) hw
       have h1 := separation_triangle (P.embed (P.parent a)) a (P.embed (P.parent b)); have h2 := separation_triangle a b (P.embed (P.parent b)); rw [separation_comm _ a] at h1; change P.count.val*K'^2+ P.count.val ≤ _ at hp; omega
lemma shelter_test (hk:n ≤ b)(hi:b ≤ i)(B:Census (R! b))(X':Stock.Tabs C.path.levels)
    (hx:∀ s:B.Mode,2 ≤ s.val.card → ∀ p∈s.val, ∀ q∈s.val,p≠q → (C.path.levels.budget b).B^2+1 ≤ separation (tree x r|>.supportX b p) (tree x r|>.supportX b q)) :
    Drake (masts x r hk B (i+1)) (pB i).B ((λ₀ i p|>.ratio.parent) ∘ ((A).supportX (i+1))):=by
    unfold masts; rw [dif_pos (hi.trans i.le_succ)]; refine ⟨fun s h h₁ hh h₂ hz he=>?_⟩
    let u:= shelter x hk (hi.trans i.le_succ); have hS:Lit B u s.val:= (Finset.mem_filter.mp s.property).2
    have hY:= hx hS.climb (hS.keep_count.symm ▸ h) (u h₁) (Finset.mem_image_of_mem _ hh) (u h₂) (Finset.mem_image_of_mem _ hz) (fun e=> he (hS.2 hh hz e))
    suffices hp : ∀ j: (ManyStem C x (i+1)),u j|>.val.2=(Θ hi p).parent ((λ₀ i p|>.ratio.parent) ( (A).supportX (i+1) j)) by
        change _ ≤ separation (u h₁|>.val.2) (u h₂|>.val.2) at hY; rw [hp,hp] at hY
        exact (_root_.Nat.le_succ _).trans (isolation X' hi _ _ hY)
    intro j; exact parent_nested _ _ _ (C.S.toDepth_odd hi p) (C.S.block_odd i) _
end Mine
end YM.RG05Readout.Many
