import YM.RG05Readout.Many.Beam
import YM.Next.RANK.Coordinates
/-!
# Node plan from all ancestors

No sector shape LIMIT assumed. This is on actual address labels and real
Moves. `bottom` labels are distinct even with same fine root in launch copies.
After closing to b, collide actual Census alternatives only with a license.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {n m p N d:ℕ} {W:Type}[Fintype W] [DecidableEq W]
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {j b k i:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "X"=> C.path
local notation "Y"=> C.path.rep N p
local notation "O"=> Address.Bud C p
local notation "λ₀"=> C.path.levels.clock.op
local notation "Θ"=>C.S.toDepth
local notation "g"=>C.path.levels.clock.J

variable (x:W→Site (C.side n p))
abbrev ManyStem (C:Family G){n p:ℕ}{W:Type} (x: W→Site (C.side n p))(i:ℕ) := { a : W×Site (C.side i p)// ∀ h:n ≤ i,(C.S.toDepth h p).parent a.2=x a.1}
local notation "R"=>ManyStem C x
variable (r:W→Motion)
def Mine.grow (h:n≤ i) (v:R i)(b: Address.Bud C p i):R (i+1):= by
    let A:= (λ₀ i p).ratio
    let x':=affine (r v.val.1).1 (A.embed v.val.2) (Address.child C p i b)
    have hp:A.parent x'=v.val.2:=by unfold x'; rw [Local.parent_affine _ (C.S.block_odd _),Address.Bud.personal]; simp [affine]
    exact ⟨(v.val.1,x'), fun h'=> ((parent_nested (Θ h p) A (Θ h' p) (C.S.toDepth_odd h p) (C.S.block_odd i) x').trans (by rw [hp]; exact v.property h))⟩

omit [Fintype W] [DecidableEq W] in
lemma rootKeeps (h:n ≤ i)(v: ManyStem C x i)(b:Address.Bud C p i): (λ₀ i p|>.ratio.parent) (Mine.grow x r h v b).val.2=v.val.2:=by
   change (λ₀ i p|>.ratio.parent) (affine (r v.val.1).1 _ (Address.child C p i b))=_; rw [Local.parent_affine _ (C.S.block_odd _),Address.Bud.personal]; simp [affine]
omit [Fintype W] [DecidableEq W] in
lemma Mine.bij (h:n ≤ i) : Bijective (Function.uncurry (Mine.grow x r h)):=by
    let P':= (λ₀ i p).ratio; let f:=Function.uncurry (Mine.grow x r h)
    constructor
    · rintro ⟨u,b⟩ ⟨v,c⟩ H; change Mine.grow x r h u b= Mine.grow x r h v c at H; have hj:= congr_arg Subtype.val H; have hv : u.val.1=v.val.1:= congr_arg (fun i': W × Site (C.side (i+1) p)=> i'.1) hj; have htX : ∀ (iU:R i) l,P'.parent (Mine.grow x r h iU l).val.2=iU.val.2:= rootKeeps x r h
      have hg: u.val.2= v.val.2:=by rw [← htX u b,H,htX]
      obtain rfl:u=v:= Subtype.ext (Prod.ext hv hg)
      congr 1
      have he:= (turnSites (r _).1 ((P').embed u.val.2)).injective (congr_arg Prod.snd hj)
      exact congr_arg Prod.snd (P'.assemble_bijective.1 he)
    intro i'
    let u:R i:=⟨(i'.val.1,P'.parent i'.val.2),by intro v; dsimp only; rw [← parent_nested]; exact i'.property (h.trans i.le_succ); exact C.S.toDepth_odd h p; exact C.S.block_odd i⟩
    let x':=i'.val.2; let e:=turnSites (n:=C.side (i+1) p) (r i'.val.1).1 (P'.embed (P'.parent x'))
    let a:=e.symm x'; have he:e a=x':= e.apply_symm_apply x'; have hp: P'.parent a=0:=by
       have ht:=parent_affine P' (C.S.block_odd i) (r i'.val.1).1 (P'.parent x') a
       rw [show affine (r i'.val.1).1 (P'.embed (P'.parent x')) a =x' from he] at ht; exact (turnSites (r i'.val.1).1 (P'.parent x')).injective (show affine (r i'.val.1).1 (P'.parent x') (P'.parent a)=affine (r i'.val.1).1 (P'.parent x') (0:Site (C.side i p)) from by rw [← ht]; simp [affine])
    let b:=P'.residue a; have hv: Address.child C p i b=a:=by
       change P'.assemble (0,b)=a; rw [← hp]; exact P'.unpack_at a
    exact ⟨(u,b),Subtype.ext (Prod.ext rfl (show e (Address.child C p i b)=x' from hv ▸ he))⟩

-- default instances `classical` on ManyStem automatically. Does not assume nonempty W; inherit from lambda.

def Mine.tree : Planner C p n (ManyStem C x) W where
    labelY _ i := i.val.1
    supportX _ i:=i.val.2
    motion:= r
    narrows _ h:= (Equiv.ofBijective _ (Mine.bij x r h)).symm
    loyal i hi u:=by
       let f:=(Equiv.ofBijective _ (Mine.bij x r hi)); let b:=f.symm u; have he:f b=u:= f.apply_symm_apply u
       change u.val.1=b.1.val.1; exact congr_arg Prod.fst (congr_arg Subtype.val he.symm) -- maybe
    future i hi u:=by
       let f:=(Equiv.ofBijective _ (Mine.bij x r hi)); exact congr_arg Prod.snd (congr_arg Subtype.val (f.apply_symm_apply u).symm)


section usage
lemma keep_occ (h:n≤ i){k:ℕ}(hx:Occupancy x k): Occupancy ((Mine.tree x r).supportX i) k:=by
    intro j
    let a:=(Mine.tree x r); let s:=Finset.univ.filter (fun x=> a.supportX i x=j)
    let b:= (Θ h p).parent j
    calc s.card= (s.image (a.labelY i)).card:= Eq.symm (card_image_of_injOn (fun p hp q hq h=>Subtype.ext (Prod.ext h ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm))))
         _ ≤ (Finset.univ.filter (fun i=> x i=b)).card:=Finset.card_le_card (by intro i h'; obtain ⟨k,hK,rfl⟩:=mem_image.mp h'; exact mem_filter.mpr ⟨Finset.mem_univ _,(k.property h).symm.trans (congr_arg (Θ h p).parent (mem_filter.mp hK).2)⟩)
         _ ≤ k:= hx _
lemma Planner.pays {V:ℕ→Type}{W:Type*}[∀ i,Fintype (V i)][∀ i,DecidableEq (V i)] (A:Planner C p n V W)(hX:Occupancy (A.supportX i) k)(h:n ≤ i): Occupancy ((λ₀ i p|>.ratio.parent) ∘ (A.supportX (i+1))) (k * (C.S.block i).val^4):=by
   intro j
   let l:=(A.narrows i h); let s:=Finset.univ.filter fun i'=> A.supportX i i'=j
   let t:=Finset.univ.filter fun i'=>((λ₀ i p|>.ratio.parent) ∘ (A.supportX (i+1))) i'=j
   have ht : t.image l ⊆ s ×ˢ Finset.univ:=by
        intro j h'; obtain ⟨i',hi',rfl⟩:=mem_image.mp h'
        have he:= parentExact (δ:=A.motion ∘ A.labelY i) (fun x=> A.future i h x); have hp:= congr_fun he i'; exact mem_product.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hp.symm.trans (mem_filter.mp hi').2⟩,Finset.mem_univ _⟩
   calc t.card= (t.image l).card:= (card_image_of_injOn l.injective.injOn).symm
        _ ≤ s.card * Fintype.card (O i):=(Finset.card_le_card ht).trans_eq (by simp)
        _ ≤ _ :=by rw [show Fintype.card (O i)= (C.S.block i).val^4 from site_card _]; exact Nat.mul_le_mul_right _ (hX _)
lemma Mine.pays {k:ℕ}(hp:n≤ i)(he:Occupancy x k)(hs:k≤ C.path.levels.clock.J n) : Occupancy (((λ₀ i p).ratio.parent) ∘ ((Mine.tree x r).supportX (i+1))) (apron Z₀ i) ∧ Occupancy ((Mine.tree x r).supportX (i+1)) (apron Z₀ i):=by
   have hz:= keep_occ x r hp he
   have h₁ := hs.trans ((Z₀).fits.mono (hp.trans i.le_succ)); have h₂ : k ≤ apron Z₀ i:=le_trans (h₁.trans ((g (i+1)).le_add_right _)) (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block i).property _)); exact ⟨fun a=> (Planner.pays (Mine.tree x r) hz hp a).trans (Nat.mul_le_mul_right _ (h₁.trans (Nat.le_add_right _ _))),fun a=> ((keep_occ x r (hp.trans i.le_succ) he) a).trans h₂⟩
end usage
end YM.RG05Readout.Many
