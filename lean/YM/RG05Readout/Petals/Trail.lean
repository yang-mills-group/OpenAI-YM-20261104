import YM.RG05Readout.Petals.Bullet
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petals
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ₀"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "R0"=> C.path.rep N p
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

local notation "L!"=> Lattice.wrap
variable {f: Extraction.Order}
-- finite differences reproduce the real joint profile on sufficiently supported arrays at weighted stencil. NO geometry restriction on relative derivative tests except to fit outer period.
abbrev Leafage (C:Family G)(d:ℕ):= Cutoffs→ Palette C d
variable (X: Leafage C d)
local notation "Ω"=>Address.Mark C
local notation "u!"=>Petals.weights
local notation "w!"=> Lattice.wrap
local notation "A"=> C.S.a
local notation "G₀"=> C.S.gridPoint
local notation "o!"=> C.S.place
noncomputable def code (m k:ℕ)(X:Leafage C d): Trial C:= ∑ i:Address.Mark C d,∑ a:Slots k,(fun N p x=> weights k i.1 a • pitch X i m N p (x+ Lattice.wrap _ (backward a)))
variable {w r}(Yc:OPE.Package C w r D)(hG:G.Simple)
include h Yc hG
lemma bids {e:ℕ}(he:e≤d)(hw:Slow C f (fun i:Cutoffs=> ((C.S.a i.1:ℂ)^(d-e))⁻¹ • X i)): Abides C f (code m k X) e∧ vet C f e (code m k X):=by
    have hp:Abides C f (code m k X) e:=by apply Adsum h hG; exact fun i _=>Adsum h hG _ _ (fun a _=> (((horn (m:=m) h X i hG he hw).native_steps a (Yc.reissue.shifts _)).scales (fun _ =>u! k i.1 a) (Slow.const _)))
    exact ⟨hp,onions h Yc.tabs Yc.system hG Yc.reissue _ hp.header hp.native (Eventually.of_forall fun _=>hp.root ..)⟩
omit h Yc hG
-- at torus budget.Power scaling Γ^slot paid exterior. Exact identity numerical supports.
lemma code_array (i:Site (C.side N p))(V:Config G (C.side N p)) : code m k X N p i V= ∑ b:Address.Mark C d, ∑ j:Slots k,weights k b.1 j* pitch X b m N p (i+ Lattice.wrap _ (backward j)) V:=by simp [code] -- maybe
private lemma real_cover (w:Cover) : G₀ N w= -(A N • away w):= by ext i; rw [PiLp.neg_apply,PiLp.smul_apply]; change _= -(A N* (-((w i:ℤ):ℝ))); rw [mul_neg,neg_neg];rfl
private lemma minus_grid (u w:Cover) : G₀ N (u-w) = G₀ N u + A N • away w:=by apply add_right_cancel (b:=G₀ N w); rw [← Work.B16.grid_add, sub_add_cancel,add_assoc,real_cover w,add_neg_cancel,add_zero]
lemma double_fit {B':ℝ}(he: B' < C.S.radius p)(x:Site (C.side N p))(a:Cover)(y:Site (C.side N p))(hp:y=x-Lattice.wrap _ a)(he': B'+ ‖(A N) • away a‖ < C.S.radius p):
   ((‖o! x+A N • away a‖≤B') ∨ ‖o! y‖≤ B') → o! y=o! x+A N • away a:=by
    let z:= o! x+A N • away a; rintro (h|h)
    · have ht: G₀ N (lift x-a)=z:= minus_grid _ _; have hx: lift y=lift x-a:= reads_grid (by rw [map_sub,wrap_lift];exact hp.symm) (ht.symm ▸ (lt_of_le_of_lt h he))
      rw [Schedule.place,hx];exact ht
    -- THIS branch is FALSE near torus boundary unless also extend B' by Δ. Need adjust
    have hf : o! y=G₀ N (lift y):=rfl; have ht: ‖G₀ N (lift y+a)‖ ≤ B'+ ‖(A N) • away a‖ := by
        rw [Work.B16.grid_add,real_cover a,←hf]; exact (norm_add_le ..).trans (by rw [norm_neg];exact add_le_add h le_rfl)
    have hx: lift x=lift y+a:= reads_grid (by rw [map_add,Lattice.wrap_lift,hp,sub_add_cancel]) (ht.trans_lt he'); refine Eq.symm ?_; change G₀ N (lift x)+ _=_; rw [← minus_grid, hx,add_sub_cancel_right];rfl

variable {V:Type}[DecidableEq V][Fintype V]
local notation "Q"=> Forms k V
local notation "Ω!"=> Cloud V
local notation "W"=> Wave V
local notation "τ₁"=> C.side N p
abbrev lattice (C:Family G)(V:Type)(N p:ℕ):= V→Site (C.side N p)
local notation "Lx"=> lattice C V N p
noncomputable def sheet (f: W) (C:Family G)(F:V→Trial C) (N p:ℕ)(U:Config G (C.side N p)) :ℂ:= (∏ _i : V,(C.S.a N:ℂ)^4)*∑ x:lattice C V N p, f.val (fun i=>C.S.place (x i)) * ∏ i:V,F i N p (x i) U
noncomputable def within (o: V→ℕ)(T:∀ i,Mark C (o i))(k:ℕ)(p:Wave V):ℂ:= ∑ j:Forms k V, (∏ i:V, weights k (T i).1 (j i))* p.val (fun i=>away (backward (j i)))
-- safer room: upper |x| for ALL x support, AND B + all jumps fits STRICT>0.
noncomputable def enters (x:lattice C V N p): W →ₗ[ℂ] W:= Pulse.fork (A N) (o! ∘ x)
variable (u:Wave V){B':ℝ}
-- aperture one step cost
omit [DecidableEq V] in
lemma wrapped_views (hV: ∀ x∈ Function.support u.val, ‖x‖≤ B') (he:B' < C.S.radius p) (x:Lx)(a:V → Cover)(hA: ∀ i, B'+ ‖A N • away (a i)‖< C.S.radius p):
    let y:= x-fun i=> w! _ (a i)
    u.val (fun i=> C.S.place (y i))=(enters x u).val (fun i=>away (a i)):=by
       intro y; let f:=fun i:V=> o! (y i); let g:=(C.S.place ∘ x)+(C.S.a N) • fun i:V=> away (a i)
       have hP(i) (hp:‖g i‖ ≤ B' ∨ ‖f i‖ ≤B') : f i=g i:= double_fit (B':=B') he (x i) _ (y i) rfl (hA i) hp
       change u.val f=u.val g
       by_cases hm:u.val g=0
       · by_cases hk:u.val f=0; exact hk.trans hm.symm
         exact congr_arg u.val (funext fun i=> hP i (Or.inr ((norm_le_pi_norm _ _).trans (hV _ hk))))
       exact congr_arg u.val (funext fun i=> hP i (Or.inl ((norm_le_pi_norm _ _).trans (hV _ hm))))
variable (s:V→ℕ) (Z': (i:V)→Leafage C (s i))
local notation "Z!p"=> (fun i:V=>code m k (Z' i))
local notation "Z!"=> (fun i:V=>Z' i (N,p))
local notation "V!"=> (i:V)→ Mark C (s i)
def hammer (T:V!)(i:V)(x:Site τ₁)(v:Config G τ₁):= pitch (Z' i) (T i) m N p x v
local notation "W!"=> hammer (m:=m) s Z'
local notation "h₀"=> (∏ _i:V,(C.S.a N:ℂ)^4)
lemma painted (v:Config G τ₁) : (Pulse.multi C m N p s Z!) u v= h₀* ∑ x:Lx,∑ i: V!, (perform s (fun j=>(i j).1) (enters x u)).val 0*(∏ j:V,W! i j (x j) v):=by
    unfold Pulse.multi; rw [LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul]; let h(v':V):=gate C m N (s v')
    rw [show (∏ i:V,h i)=h₀ * ∏ i:V, magnify C m N (s i) from Finset.prod_mul_distrib,mul_assoc]; apply congr_arg; simp only [LinearMap.sum_apply,Finset.sum_apply]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; change (∏ i:V,magnify C m N (s i))* (∑ j:V!,_) = _; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; unfold hammer pitch; simp only [Pi.smul_apply,smul_eq_mul,prod_mul_distrib]; rw [mul_left_comm];rfl
lemma act (x: Lx)(v:Config G τ₁): (∏ i:V,(code m k (Z' i)) N p (x i) v)=∑ j:V!,∑ b: Forms k V,∏ i:V,(weights k (j i).1 (b i)*W! j i (x i+ w! _ (backward (b i))) v):=by
     -- multi sum via Fintype.prod_sum'.
     let f(i:V)(j:Address.Mark C (s i) × Slots k):=weights k j.1.1 j.2* pitch (Z' i) j.1 m N p (x i+ w! _ (backward j.2)) v
     have ht (i:V):code m k (Z' i) N p (x i) v=∑ j:(Address.Mark C (s i) × Slots k), f i j:=by rw [code_array,Fintype.sum_prod_type]
     simp_rw [ht]; rw [Fintype.prod_sum];
     let U: V! × Forms k V ≃ ((i:V)→Address.Mark C (s i) × Slots k):= -- syntax parentheses
         {toFun:=fun x i=>(x.1 i,x.2 i), invFun:=fun i=>(fun a=>(i a).1,fun a=>(i a).2), left_inv:=fun p=>rfl,right_inv:=fun p=>rfl}; rw [← Equiv.sum_comp U,Fintype.sum_prod_type];rfl
set_option maxHeartbeats 400000 in
lemma painting (v:Config G τ₁) (hp:∀ x∈Function.support u.val,‖x‖≤ B')(he:B' < C.S.radius p) (hB: ∀ j:Slots k, B'+ ‖(C.S.a N) • away (backward j)‖< C.S.radius p):
    sheet u C Z!p N p v=h₀ * ∑ x:Lx,∑ i: V!, within s i k (enters x u)*(∏ j:V,W! i j (x j) v) :=by
    unfold sheet; apply congr_arg; simp_rw [act (N:=N) (p:=p) s Z', Finset.prod_mul_distrib, within,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s:=Finset.univ (α:=Lx))]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm, Finset.sum_comm (s:=Finset.univ (α:=Lx))]; refine Finset.sum_congr rfl (fun j _=> ?_)
    let w:Lx:=fun i=> Lattice.wrap _ (backward (j i)); let f:=Equiv.subRight w; rw [← Equiv.sum_comp f]; refine Finset.sum_congr rfl (fun x _=> ?_); let b':=∏ l:V, W! i l (x l) v
    rw [show (∏ l:V, W! i l (f x l +w l) v)=b' from Finset.prod_congr rfl (fun l _=> by rw [show f x l + w l=x l from sub_add_cancel ..])]; rw [show u.val (fun i=> C.S.place (f x i)) = _ from wrapped_views u hp he x (fun i=> backward (j i)) (fun i=>hB _)]; change _*(_*b')= (_*_)*b'; rw [←mul_assoc,mul_comm ((enters x u).val _)]
end YM.RG05Readout.Petals
