import YM.RG05Readout.Bay.Shrine
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow Flatten Nuclear Halls Pulse
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}(h:C.Makes)
set_option quotPrecheck false
open Extraction
local notation "α!"=> C.S.a
open Metric

/-!
Audibility with normalizing measure and UNIT price externally. For any centered field in prepaid cell need real correlation test with Poem. Tensor plugs physically at each actual spectator point. Sew with translation-compatible pin's seam corners; no center equivariance of g-stencils required to test signed credit. 
-/
open Dash Extraction.Lease
open UVExt UVExt.Slots Push.RelayDifference
variable (D:Poem C j)
local notation "I"=> Fin D.n
local notation "Z"=> C.side N p
local notation "y"=> D.token
local notation "α₁"=> C.S.a N
local notation "T"=> Cells.center
variable {f: Extraction.Order}(hp:CenterPort C f)
def column (N p:ℕ)(x: Fin D.n →Site (C.side N p))(g:Goods G (C.side N p)) := moment (C.beta N p) (fun U=>g U*∏ i,C.seen (D.token i) (x i) U)
def drum (x: I → Site (C.side N p)) (i:I):= (D.post i).val (C.S.place (x i))
abbrev preamble (N p:ℕ)(g:Goods G (C.side N p)):= (C.S.a N:ℂ)^(4*D.n)* ∑ x:I→Site (C.side N p),(∏ i:I,(D.post i).val (C.S.place (x i))) * column D N p x g
local notation "κ"=> Lattice.wrap
include h hp
lemma drums : ∃ A:ℝ,0 ≤ A ∧ ∀ᶠ i in f.fuse, ∃ hv:j ≤ i.fst, ∀ x:I→ Site (C.side i.1 i.2), (∀ k,x k∈D.annulus i.1 i.2 k) → ∀ g:Goods G (C.side i.1 i.2), Interior ((T C.S i.2 hv 0).chamber 0) g→ ‖column D i.1 i.2 x g‖≤ (T C.S i.2 hv 0).rootTest (C.beta i.1 i.2) g * A:=by
    let F(k:I):= Bid.visits C (y k).1 (y k).2
    have hz(k): TiledCaps C f (F k):=from_tight h hp ⟨‖(y k).2‖,Eventually.of_forall fun _=>Eventually.of_forall fun _=>le_rfl⟩
    choose B hB hi using fun i=> hz i j 8 (by decide) 
    have hf:∀ᶠ i in f.fuse, Injective (κ (C.side j i.2) ∘ D.key):=by rw [Order.fused]; exact (f.per.cofinal.eventually D.placed).mono (fun j hj=> Eventually.of_forall fun _=> hj)
    have ht(i): ∀ᶠ c in f.fuse,literal (F i c.1 c.2):= (Stencilled.visits h _|>.literal)
    refine ⟨∏ i:I,B i,Finset.prod_nonneg (fun i _=>hB i),?_⟩
    have hk(i:I): ∀ᶠ c in f.fuse, ∃ he:j ≤ c.1,∀ T₁:Tiling (C.side c.1 c.2),T₁.side.val=Cells.span C.S he c.2→ T₁.kind=Kind.link→ priceAt (F i c.1 c.2 0) («T»:=T₁) 8 (C.beta c.1 c.2) (B i) := (Order.fused f _).2 (hi i)
    filter_upwards [eventually_all.mpr hk,hf,eventually_all.mpr ht,(cutoff_grows f).eventually_ge_atTop j] with u hx hh hu ht; let N:=u.1; let p:=u.2
    refine ⟨ht,fun x ho g hG=>?_⟩; let Z₀:= (T C.S p ht 0); let z:= κ (C.side j p) ∘ D.key
    have hW (i:I) : ∃ U:Goods G (C.side N p), Interior (Z₀.chamber 0) U∧ Z₀.copy (z i.succ) U=F i N p (x i)∧ Z₀.rootTest (C.beta N p) U ≤ B i:=by
       let a:=z i.succ; let b:= (Z₀.omega a)⁻¹; let t:=decide (Z₀.hand a)
       obtain ⟨y₀,hz'⟩:= Z₀.pointed a (x i); have hk:y₀∈ Z₀.margin 0 (Z₀.side.val/8):= (Z₀.reflected_margin y₀ a _).2 (by rw [hz']; exact D.annulus_fits ht i (ho i))
       obtain ⟨hw',hR⟩:= (hx i).choose_spec Z₀ rfl rfl _ hk t b (diag_inv (by rfl)); refine ⟨_, hw',?_,hR⟩; dsimp only [t,b]; rw [copied,mul_inv_cancel,hz',Bool.xor_self]; exact (unorient (hu i) _).symm
    choose Uv hV hν hv using hW
    let U:= Fin.cons (α:=fun _=>Goods G (C.side N p)) g Uv; let b₀:= C.beta u.1 u.2
    have hZ:column D N p x g= moment b₀ (fun X'=> ∏ i, Z₀.copy (z i) (U i) X'):=by
       unfold column; congr 1; funext v; rw [Fin.prod_univ_succ, show U 0=g from Fin.cons_zero ..,show z 0=(0:Z₀.Cell) from (by change Lattice.wrap _ (D.key 0)=(0:Site (C.side j p));rw [D.centered,map_zero]),Tiling.copy_zero]; congr 1; refine Finset.prod_congr rfl fun j _=> ?_; rw [show U j.succ=Uv j from Fin.cons_succ ..,hν j];rfl
    rw [hZ]; refine (Z₀.planted (seamless h ..) _ hh U (fun i=> ?_)).trans ?_
    · refine Fin.cases ?_ (fun j=> ?_) i; rw [show U 0=g from Fin.cons_zero ..]; exact hG; rw [show U j.succ= Uv j from Fin.cons_succ ..]; exact hV _
    rw [Fin.prod_univ_succ]; simp_rw [U,Fin.cons_zero,Fin.cons_succ]; exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=> Z₀.root_nonneg ..) (fun i _=>hv i)) (Z₀.root_nonneg ..)

lemma leaning : ∃ A:ℝ,0 ≤ A∧ ∀ᶠ i in f.fuse, ∃ hv:j ≤ i.fst,∀ g:Goods G (C.side i.1 i.2), Interior ((T C.S i.2 hv 0).chamber 0) g→ ‖preamble D i.1 i.2 g‖≤ A * (T C.S i.2 hv 0).rootTest (C.beta i.1 i.2) g:=by
    obtain ⟨A,hA,hX⟩:= drums h D hp; let K:=4*D.n; let s:= C.S.a j; have ht:s>0:= C.S.a_pos _
    refine ⟨s^K*A,mul_nonneg (pow_nonneg ht.le K) hA,?_⟩
    filter_upwards [hX] with i hi; obtain ⟨hv,hC⟩:= hi; let L:=C.S.toDepth hv i.snd; let N:=i.fst; let p:=i.snd; let T':= T C.S i.2 hv 0; let l:ℕ:= L.count.val; let t:=C.S.a N; have hx : t*l=s:= C.S.embeds_scale _
    refine ⟨hv,fun g hG=>?_⟩; let q:= T'.rootTest (C.beta N p) g
    let W:= Fintype.piFinset fun k:I=> D.annulus N p k
    let X (x:I→Site (C.side N p)) := (∏ i,drum D x i) * column D N p x g
    have hy: preamble D i.1 i.2 g = (t:ℂ)^K * ∑ x∈W,X x:=by
        unfold preamble; apply congr_arg ((t:ℂ)^K * ·); apply Eq.symm (Finset.sum_subset (f:=X) (Finset.subset_univ W) (fun x _ h=> ?_)); obtain ⟨j,hj⟩:= not_forall.mp (mt Fintype.mem_piFinset.mpr h); unfold X; rw [Finset.prod_eq_zero (Finset.mem_univ j) (image_eq_zero_of_notMem_tsupport (f:=(D.post j).val) (fun H=> hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩))),zero_mul] -- types ambiguity
    have he(k:I)(x:I→Site (C.side N p)):‖drum D x k‖ ≤ 1:=by
       unfold drum; change ‖(((D.singer k.succ (C.S.place (x k))):ℝ):ℂ)‖≤ _; rw [Complex.norm_real,Real.norm_of_nonneg (D.singer k.succ).nonneg]; exact (D.singer k.succ).le_one
    have hq(x)(hz:x∈ W): ‖X x‖ ≤ q*A:=by
        unfold X; rw [norm_mul, norm_prod]; exact (mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun i _=> he i x))).trans (hC x (Fintype.mem_piFinset.mp hz) _ hG)
    have hc: W.card ≤ l^K:= by
        unfold W; rw [Fintype.card_piFinset]; refine (Finset.prod_le_prod (g:=fun _=>l^4) (fun _ _=>Nat.zero_le _) fun k _=>D.annulus_count hv k).trans_eq ?_; simp [K,pow_mul]
    have ht':0 ≤ t:= (C.S.a_pos _).le; rw [hy,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht']
    refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum hq)) (pow_nonneg ht' _)).trans ?_; rw [Finset.sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (show (W.card:ℝ) ≤ (l:ℝ)^K from by exact_mod_cast hc) (show 0 ≤ q*A from mul_nonneg (T'.root_nonneg ..) hA)) (pow_nonneg ht' K)) _; rw [←hx,mul_pow]; change t^K*((l:ℝ)^K*_ )≤ _*q; apply le_of_eq;ring
end YM.RG05Readout.Bay
