import YM.RG05Readout.Records.Charged
/-!
# Trace a live native body derivative and pay its support

Sites toric all the way. Root a point for the *relative* location in cover:
actual law evaluations pull every sector through odd parent step. Take ANY j'th
functional; if child active then parent touched in the native span at offset
adopted. No independence assumption for daughter values. Exhibits lifts of
surviving final roots, with orientation covariance to registered parent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g:ℕ}
set_option quotPrecheck false
local notation "S'"=> C.S
local notation "Πξ"=> C.S.toDepth
local notation "ψ"=> C.path.levels.clock
local notation "K"=> C.path.levels.clock.op
local notation "α"=> C.S.a
local notation "G!"=> C.S.gridPoint
local notation "λ!"=> C.side
local notation "Z!"=>C.path.levels.budget
section
variable (x:I→Site (C.side n p)) (T:I→Motion)(W:ManyStem C x n→Body)
local notation "M₀"=> ManyStem C x
local notation "Ω"=>Mine.tree x T
local notation "F"=> headings x T W
local notation "s₁"=> (C.S.block i).val
lemma step_point (w:Cover): G! (i+1) (s₁ • w)= G! i w:=by
    apply PiLp.ext; intro k; rw [Schedule.gridPoint,C.S.a_step]; change ((C.S.a i)/(s₁:ℝ))*(((s₁:ℕ) • w k:ℤ):ℝ)=_
    rw [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; change (_:ℝ)*(s₁* _)=(α i)*(w k); field_simp
lemma step_shift (w:Cover)(z:Address.Bud C p i) (t:E4):
    G! i w + (α i) • (displacement C p i z+((s₁:ℝ)⁻¹) • t)= G! (i+1) (s₁ • w + lift z)+(α (i+1)) • t :=by
    rw [Work.B16.grid_add (C:=C),step_point,Schedule.a_step,smul_add,smul_smul,← add_assoc, ← div_eq_mul_inv]
    congr 2
    unfold displacement; rw [smul_smul]; apply PiLp.ext; intro j; change (((α i)*((s₁:ℝ)⁻¹)) • (lift z j:ℝ))= (α (i+1))*(lift z j); rw [Schedule.a_step,← div_eq_mul_inv]; rfl
lemma embed_shift (w:Cover)(z:Address.Bud C p i)(t:Motion) (r : Site (C.side i p)): let Q:=(C.path.levels.clock.op i p).ratio; let y:= affine t.1 r (Lattice.wrap _ w)
    affine t.1 (Q.embed y) (Address.child C p i z)=affine t.1 (Q.embed r) (Lattice.wrap _ ((s₁:ℕ)• w + lift z)):=by
    intro Q y; unfold y; rw [Records.pole]
    unfold Address.child; change affine _ _ (Q.assemble (0,z))=_
    rw [Ratio.assemble,map_add, show Q.embed 0=0 from Q.root.map_zero,zero_add,Q.embed_wrap]; unfold affine; rw [Signed.act_add, add_assoc, add_left_comm]
    rfl
omit [DecidableEq I][Fintype I] in
lemma traces (he:n ≤ i)(j: M₀ i){ϕ:E4}{t:ℕ}(hh:ϕ∈Native.box) (hp:iteratedFDeriv ℝ t (headings x T W i j).val ϕ ≠ 0)(o:Site (C.side n p))(w:Cover)(hx:x j.val.1= affine (T j.val.1).1 o (Lattice.wrap _ w)) :
   ∃ (u:Cover)(a:E4), j.val.2= affine (T j.val.1).1 ((Πξ he p).embed o) (Lattice.wrap _ u) ∧ a∈ Native.box∧ G! n w+(α n) • a=G! i u+(α i) • ϕ ∧ iteratedFDeriv ℝ t (headings x T W n ((Mine.remap x T).symm j.val.1)).val a≠0:=by
     induction i,he using Nat.le_induction generalizing ϕ with
     | base => exact ⟨w,ϕ, by rw [Records.like_embed]; exact (Mine.carried x T j).trans hx,hh,rfl, fun h=>hp (by rw [show (Mine.remap x T).symm j.val.1=j from Equiv.symm_apply_apply ..] at h; exact h)⟩
     | succ i hi ih=>
        let l:=(Ω).narrows i hi; let u:=(l j).1; let v:=(l j).2; let P':=(displacement C p i v)+(((C.S.block i).val:ℝ)⁻¹) • ϕ; let L':=(Πξ hi p); let q:=(K i p).ratio; have h : j.val.1=u.val.1:= (Ω).loyal i hi j
        have htP: iteratedFDeriv ℝ t (headings x T W i u).val P' ≠ 0:=by
            intro ht; apply hp; rw [show headings x T W (i+1) j=headFee C p i v (headings x T W i u) from (Many.headlines (N:=i+1) ..).2 i hi i.lt_succ_self j]; unfold headFee; rw [Native.pulled, show iteratedFDeriv ℝ t (headings x T W i u).val _=0 from ht,smul_zero]
        obtain ⟨y,a,hu,hy,hU,hY⟩:= ih u (Address.dist_box C p i v hh) htP (h ▸ hx) -- ih argument P' generalized?
        · let L:= (C.S.block i).val; refine ⟨L • y+ lift v, a, ?_,hy,hU.trans (step_shift y v ϕ), h.symm ▸ hY ⟩
          rw [h]; rw [show j.val.2= affine (T u.val.1).fst (q.embed u.val.2) (Address.child C p i v) from (Ω).future .., hu, embed_comp L' q _]; exact embed_shift ..

omit [DecidableEq I] [Fintype I] in
lemma picked (s:I→ℕ)(hi:n≤ i)(j:M₀ i)(hv:j∉ shadow (Ω) s (F) i)(o:Site (C.side n p))(w:Cover)(hx:x j.val.1= affine (T j.val.1).1 o (Lattice.wrap _ w)) :
    ∃ (u:Cover)(a b:E4), j.val.2= affine (T j.val.1).1 ((Πξ hi p).embed o) (Lattice.wrap _ u) ∧ a∈ Native.box∧ G! n w+(α n) • a=G! i u+(α i) • b ∧ b∈ Native.box∧ a∈tsupport (W ((Mine.remap x T).symm j.val.1)).val:=by
     unfold Many.shadow at hv; change ¬ Cap _ _ _ at hv; unfold Cap at hv; push Not at hv
     obtain ⟨k,h,a,h_a,hA⟩:= hv; obtain ⟨y,u,hP,hv,ht,hf⟩:= traces x T W hi j h_a (norm_pos_iff.mp hA) o w hx
     refine ⟨y,u,a,hP,hv,ht,h_a,support_iteratedFDeriv_subset k (?_ : iteratedFDeriv ℝ k (W ((Mine.remap x T).symm j.val.1)).val u ≠ 0)⟩
     rwa [← (Many.headlines (N:=0) x T W).1]
end

end YM.RG05Readout.Halls
