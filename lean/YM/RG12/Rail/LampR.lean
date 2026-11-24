import YM.RG12.Rail.ReachR
import YM.RG12.Roof.Ellipse
/-! Joint reflection on RAY. Port the short Lava/Compose argument to new
  geometric quantifiers without interlacing cheap grids or making a new sublimit;
  now across ANY lattice length test along prespecified rational ray. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}{l:Filter UVIndex}[l.NeBot] {M:∀ d, ℕ→RepChart C d}
  {d n D k N p m:ℕ}
  {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z) (x:ι)
local notation "a!"=> (P x).arc

/- raw estimate from lava_v. Compare *any* y, even on potentially redundant lists (using
full rank estimate machinery). Only call for m = 1 below. -/
include H h hp hZ
open YM.RG12.Rail
variable {a₀:Points (m+1)}
local notation "kr" k:max=> {i:Points (m+1)|Anemos a₀ ((A).clock.monitor k) i}
-- tail of Reach proof

variable {t :Fin (m+1)→Fin (D+1)} (y: (i:Fin (m+1))→ C.label (t i))

omit [Fintype ι]
lemma lava_R (hLu:a₀∈conf (m+1)) (hn:2≤n)(hn':m+1 ≤ n) : ∀ᶠ k:ℕ in atTop,
    ∀ T,Poised P B H O J n z k T→ ∀ N p (he:k<N),
     let v(i):= ladd C (mag A a! k) k N p _ (T N p (t i)) (y i)
     ∀ (w : Points (m+1)), (tested A a! k w) ∈ kr k →∀ h:Fit A a! k w,∀ s : modes (Fin (m+1)),s.val.Nonempty →
       (Ship.yard C a! he.le p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX y) (q_asked (C:=C) (d:=fun i=> (t i).val) v) h N p U).part s) ≤ Ship.budget C.path.levels n k:=by
   filter_upwards [earningsR B H h hp O J (P x) hLu hZ (d0:=fun i=>(t i).val) y hn' hn (fun i=>Nat.le_of_lt_succ (t i).isLt) ] with k hu T he N p hN
   intro v w hw hs s hv
   let K (x:ℝ)(h:Fit A x k w):=(Ship.yard C x hN.le p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX y) (q_asked (C:=C) (d:=fun i=>(t i).val) v) h N p U).part s)
   obtain ⟨l,r,F,hF⟩:=he.supply x; obtain ⟨V,hV,hx⟩:= hF N p hN
   choose Y hy using hx
   let θ := (P x).bag ((A).clock.J k);have ha:θ.band=a!:= (P x).factor _
   have hf:Fit A θ.band k w:=ha.symm ▸ hs
   have hg(i): Price.Solves C (mag A θ.band k) _ k N p (Y (t i)).T (y i) (v i):= by
      rw [ha,hy]; exact poured H (he.early _ (Nat.le_of_lt_succ (t i).isLt)) hN.le _ _ (he.charts N p hN (t i)).1 _
   have hQ : K θ.band hf ≤ Ship.budget C.path.levels n k:= hu l r F N p hN V hV w (ha.symm ▸ hw) hf (fun i=> Y (t i)) v hg s hv
   change K a! hs ≤ _; suffices hh:∀ (h:Fit (A) a! k w), K a! h ≤ Ship.budget (A) n k from hh hs; rw [← ha]; intro h; exact hQ

omit H hp hZ in
lemma open_R (t:Points (m+1)) (b:ℝ): ∀ᶠ k:ℕ in atTop, Allowed (A) b k → ∀ x:Fin (m+1)→ Cover,
    let y:= tag (mag (A) b k)⁻¹ x
    y ∈ generic (m+1)→ Anemos t ((A).clock.monitor k) y→ Fit (A) b k y:=by
   have hp(k): Station.mag (A) 1 k=(A).clock.monitor k:=by rw [mag,Real.rpow_one]
   filter_upwards [(Station.mag_rate (A) h zero_lt_one).eventually_ge_atTop (8*‖t‖)] with k hi hx x y hg ht
   have hd := (authentic (V:=A) (b:=b) (k:=k) x).2
   have hq : Next.Rank.Station.key (A) b k y=gap (A) b k • y := by rw [Next.Rank.Station.anchored,show Next.Rank.Station.tested (A) b k y=y from hd]
   have hv : 0<gap (A) b k:=gap_pos ..
   constructor
   · rw [hq]; exact scales_wild hv _ hg
   intro i j; rw [hq]; change |gap (A) b k * y i j| ≤ _; rw [abs_mul,abs_of_pos hv]
   obtain ⟨s,hs,ho⟩:=ht; let μ:=(A).clock.monitor k
   have hh : 0 ≤ μ:= Real.exp_nonneg _
   have he: |y i j| ≤ μ*‖t‖:=by
      have h:= (PiLp.norm_apply_le (y i) j).trans ((PiLp.norm_apply_le y i)); rw [ho,norm_smul,Real.norm_of_nonneg (zero_le_one.trans hs.1)] at h
      rw [Real.norm_eq_abs, show (s • t) i j= _ from (rfl: (s • t) i j=s*t i j)] at h
      rw [ho]; exact h.trans (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg t))
   have hP:=hx.dilation; rw [le_div_iff₀ (C.S.a_pos _)] at hP; have hB:8*‖t‖ ≤ μ:= hi.trans_eq (hp _)
   unfold gap at *; change Station.mag _ _ _*μ^2*C.S.a k ≤ _ at hP
   have h:8* |y i j| ≤ μ^2:=by nlinarith [mul_le_mul_of_nonneg_left hB hh]
   linarith only [hP,mul_le_mul_of_nonneg_left h hv.le]
-- uniform price *for the queried ray*, despite x moving. compact by anemometer staging.
omit H h hp hZ in
lemma profiles_bounded (t: Points (m+1))(U:Fin (m+1)→(Cells.standard C).Tag)(ht:t∈conf _): ∃ K:ℝ, 0≤K∧ ∀ s:ℝ,1 ≤ s→
   Poly.price (fun _=>1) (Read.maxProfile C (s • t) U) ≤ K:=by
   let O' (s:ℝ):= Poly.price (fun _=>1) (Read.maxProfile C (s • t) U)
   by_contra! h
   choose a ha hz using fun n:ℕ=> h (n:ℝ) (Nat.cast_nonneg _)
   obtain ⟨u,hu,p,hp,hU⟩:=isCompact_Icc.isSeqCompact (s:=Icc (0:ℝ) 1) (x:=fun n=>(a n)⁻¹) (fun n=> Set.mem_Icc.mpr ⟨by have hf:=ha n; positivity,inv_le_one_of_one_le₀ (ha n)⟩)
   obtain ⟨z,hz'⟩:=profile_wind t ht (a ∘ p) (fun i=>ha (p i)) hU U
   let k:ℝ:=Poly.price (fun _=>1) z
   have he:Tendsto (fun i:ℕ=>O' (a (p i))) atTop (𝓝 k):=by
      apply tendsto_finsetSum _ (fun j _=>tendsto_const_nhds.mul ((tendsto_pi_nhds.1 hz' j).norm))
   obtain ⟨j,hj,hk⟩:= ((he.eventually (ge_mem_nhds (lt_add_one k))).and ((tendsto_natCast_atTop_atTop.comp hp.tendsto_atTop).eventually_ge_atTop (k+1))).exists; have ho:O' (a (p j))>p j:=hz _ -- syntax
   simp only [Function.comp_apply] at hk; linarith only [ho,hk,hj]
lemma literalR (t:Fin (m+1) → Fin (D+1)) (y:(i:Fin (m+1))→ C.label (t i)) (hR:a₀∈conf _)(hn:2≤n)(hn':m+1≤n)
    (f:Extraction.Order) :
    ∃ c:ℝ,0≤ c ∧ ∀ᶠ k in atTop, ∀ T, Poised P B H O J n z k T→
      ∀ i:Fin (m+1)→ Cover, let y₀:= tag (mag A a! k)⁻¹ i; y₀∈ kr k→y₀∈ generic _→ f.late fun N p=>
      let v j:= ladd C (mag A a! k) k N p (t j) (T N p (t j)) (y j)
      ‖C.numeric N p (q_asked (C:=C) v) (fun x=>location C.S k N p (i x))-disc (jointX y) y₀‖ ≤ c*Ship.budget A n k:=by
  let O' (r):= Poly.price (fun _=>1) (Read.maxProfile C r (jointX y))
  obtain ⟨c,hc,hT'⟩:= profiles_bounded _ (jointX (C:=C) y) hR
  have ha:0<a!:= by have hh:=(P x).huge; linarith [Nat.cast_nonneg (α:=ℝ) D]
  refine ⟨max c 0, le_max_right ..,?_⟩
  filter_upwards [lava_R P B H h hp O J z hZ x y hR hn hn', open_R (C:=C) h a₀ a!] with k he ht T hT i q hr hΓ
  obtain ⟨h1,h2⟩:= authentic (V:=A) (k:=k) (b:=a!) i
  have hA:Allowed A a! k:=by obtain ⟨l,r,u,h⟩:= hT.supply x; rw [← (P x).factor ((A).clock.J k) ]; exact u.age.allot.permitted
  have hv:Fit A a! k q:= ht hA i hΓ hr
  unfold Order.late
  refine Eventually.of_forall fun l=> ?_
  have qc := f.mesh.cofinal.eventually (eventually_all.mpr (fun r : Fin (m+1)=>hv.stencils (F:=C) H (t r)))
  filter_upwards [qc, f.mesh.cofinal.eventually_gt_atTop k] with j hj hx
  let Q:=f.mesh j;let p:=f.per l
  let v:(j:Fin (m+1))→ C.label (t j):=fun j => ladd C (mag A a! k) k Q p (t j) (T Q p _) (y j); let W:= q_asked (C:=C) v
  have hg: ∀ s,s.val.Nonempty→ (Ship.yard C a! (show k≤ Q from hx.le) p).rootTest (C.beta Q p) (fun U=> (Ship.invoice (jointX y) W hv Q p U).part s) ≤ Ship.budget (A) n k:=he T hT Q p hx q (h2.symm ▸ hr) hv
  have hG:∀ j,Interior _ (Read.probes C Q p k (Next.Rank.Station.choose (A) a! k q) W j):=fun j=> (hj j).choose_spec p j (v j)
  have hm:= (Ship.budget_pos (A) n k).le
  have hf:= Read.full_cost H (Ship.fitting hv) hm (Ship.yard C a! (show k ≤ Q from hx.le) p) hG hg
  change Next.Rank.Station.choose A a! k q=i at h1; change Next.Rank.Station.tested A a! k q=q at h2; rw [h1,h2] at hf
  apply hf.trans
  obtain ⟨s,hs,he⟩:=hr; rw [he]; exact mul_le_mul_of_nonneg_right ((hT' s hs.1).trans (le_max_left ..)) hm


variable {S : Table C.book} {f: Extraction.Order}
omit H h hp hZ in
private lemma boxed {L : Register G} (S : Table L){j i:ℕ} (x : Points 2) (h:S.Symmetric) (hv:x∈conf _) (v:L.Vector ![j,i]) :
   S.value ![j,i] x v=disc ![(⟨j,S.project j (v 0)⟩:S.Tag),⟨i,S.project i (v 1)⟩] x:=by
   let t:=fun r:Fin 2=> (⟨![j,i] r,v r⟩:L.Token)
   have hf: ![(⟨j,S.project j (v 0)⟩:S.Tag),⟨i,S.project i (v 1)⟩]=S.classTokens ∘ t:=by funext q; fin_cases q<;>rfl
   rw [hf]; exact (S.at_project S h (fun _ => by tauto) hv t).symm -- sig?

/- Compare at the true length, in the unselected physical field quotient of S. Don't take a
  cutoff filter across moving k inside this statement (Poised only prices fixed k in the
  filter limit). In this view varying actual regulator lists with k are accounted through the
  FUSE data for all k and lamps read at any one scale at a time.
-/
lemma at_R (hP:f.PointLimits C S) (hh:S.Symmetric)
    (hobs:Observing C H ϕ M)(hb: ϕ≤ f.fuse) (j i : Fin (D+1)) (v : C.label j)(w:C.label i)
    {a₀:Points 2}(hR:a₀∈conf 2)(hn:2≤n) :
    ∃ c:ℝ,0≤ c ∧ ∀ᶠ k in atTop,∀ T : ℕ→ℕ→TableL C D, ∀ _:Poised P B H O J n z k T,
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), Comparer (ϕ:=ϕ) (hC:=H) l k D T (mag A a! k) Z→
        ∀ b:Fin 2→ Cover, let y:= tag (mag A a! k)⁻¹ b; Anemos a₀ ((A).clock.monitor k) y → y∈generic 2→
          ‖pair S (Order.grid C k b) (S.project j (aligned C M k (Z j) v)) (S.project i (aligned C M k (Z i) w))- freePair C y v w‖ ≤ c * Ship.budget A n k:=by
  let t(j i:Fin (D+1)):= ![j,i]
  let e:(r:Fin 2) → C.label (t j i r):= Fin.cases v (Fin.cases w fun i=>Fin.elim0 i)
  obtain ⟨c,hc,Hc⟩:= literalR P B H h hp O J z hZ x (m:=1) (t j i) e hR hn hn f
  refine ⟨c,hc,?_⟩
  filter_upwards [Hc] with k hk T hT Z hC b y hy he
  have hd:= hk T hT b hy he
  let t':=![j.val,i.val]; let μ:= mag A a! k
  let W (p:UVIndex)(d:Fin (D+1)):= ladd C μ k p.1 p.2 d (T p.1 p.2 d)
  let Y (i:Fin (D+1)):=aligned C M k (Z i)
  let V:= name_pair (Y j v) (Y i w); let V₀(p:UVIndex):=name_pair (W p j v) (W p i w)
  have hv r : Tendsto (fun p=> V₀ p r) l (𝓝 (V r)):=by
    fin_cases r
    · exact tends_aligned hobs hC j v (hT.early _ j.is_le)
    exact tends_aligned hobs hC i w (hT.early _ i.is_le)
  let U:=Order.grid C k b
  have hμ:0 < μ:= Station.mag_pos ..
  have hab:(U∈generic 2):=by
    intro x' r s hX
    apply (he x')
    have h : ((b r x':ℤ):ℝ) = b s x':=mul_left_cancel₀ (C.S.a_pos k).ne' (show C.S.a k * _ = C.S.a k*_ from hX)
    change μ⁻¹*((b r x':ℤ):ℝ)=μ⁻¹*((b s x':ℤ):ℝ);rw [h]
  have hs:= OPE.Cards.variation b hP hab V V₀ hv (hC.filter_le.trans hb)
  have ht:= (hs.sub_const (freePair C y v w)).norm
  have hK(u:UVIndex):
       let c(r:Fin 2):= ladd C μ k u.1 u.2 _ (T u.1 u.2 (t j i r)) (e r)
       C.ensemble t' (fun x=>location C.S k u.1 u.2 (b x)) (V₀ u)=C.numeric u.1 u.2 (q_asked (C:=C) c) (fun x=> location C.S k u.1 u.2 (b x)):=by
     intro c
     change C.numeric u.1 u.2 (fun i=> (⟨t' i,V₀ u i⟩:C.book.Token)) _=_
     congr 2
     funext q; fin_cases q<;>rfl
  have hD:disc (jointX e) y=freePair C y v w:=by
    unfold freePair; congr 1; funext r; fin_cases r<;>rfl
  rw [show pair S (Order.grid C k b) (S.project j (aligned C M k (Z j) v)) (S.project i (aligned C M k (Z i) w))=S.value t' U V from (boxed _ U hh (generic_conf 2 hab) V).symm]
  refine le_of_tendsto ht (((show ∀ᶠ u : UVIndex in f.fuse,
     ‖C.numeric u.1 u.2 (q_asked (C:=C) (d:=fun r => ((t j i r):ℕ)) (fun r=> W u (t j i r) (e r))) (fun x=>location C.S k u.1 u.2 (b x)) - disc (jointX e) y‖ ≤ c * Ship.budget A n k from hd).filter_mono (hC.filter_le.trans hb)).mono fun i hi' => ?_)
  change ‖C.ensemble t' _ (V₀ i) - freePair _ y v w‖ ≤ _
  rwa [hD,← hK] at hi'
private def E {d:ℕ} (i : (C.labels.level d).Index) : C.label d:= Pi.single i 1
-- actually simultaneous *matrix* error. no costs per p. includes all pairs of horizons in the Poised datum.

set_option maxHeartbeats 500000 in
lemma rails (hP:f.PointLimits C S) (hh:S.Symmetric)
    (hobs:Observing C H ϕ M)(hb: ϕ≤ f.fuse)
    {a₀:Points 2}(hR:a₀∈conf 2)(hn:2≤n) :
    ∃ c:ℝ,0≤ c ∧ ∀ᶠ k in atTop,∀ T : ℕ→ℕ→TableL C D, Poised P B H O J n z k T→
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), Comparer (ϕ:=ϕ) (hC:=H) l k D T (mag A a! k) Z→
        ∀ b:Fin 2→ Cover, let y:= tag (mag A a! k)⁻¹ b; Anemos a₀ ((A).clock.monitor k) y → y∈generic 2→ ∀ (j i : Fin (D+1))(v : C.label j)(w:C.label i),
          ‖pair S (Order.grid C k b) (S.project j (aligned C M k (Z j) v)) (S.project i (aligned C M k (Z i) w))- freePair C y v w‖ ≤ c * Ship.budget A n k * mass C j v * mass C i w:=by
  choose c hc he using fun (j i:Fin (D+1)) (v:(C.labels.level j).Index) (w:(C.labels.level i).Index)=> at_R (l:=l) P B H h hp O J z hZ x hP hh hobs hb j i (E v) (E w) hR hn
  let u(i:Fin (D+1)) := (C.labels.level i).Index
  let c1(j i:Fin (D+1))(v:u j):= ∑ w:u i,c j i v w
  let c2(j i):=∑ v:u j,c1 j i v; let c3(j):=∑ i,c2 j i; let Q:=∑ j,c3 j
  have h1(j i v):0≤ c1 j i v:= Finset.sum_nonneg (fun w _=>hc ..)
  have h2(j i):0≤ c2 j i:=sum_nonneg fun v _=> h1 j i v
  have h3 j:0≤ c3 j:=sum_nonneg fun i _=> h2 j i
  have hX{ι : Type}[Fintype ι]{h:ι→ℝ}(H:∀ i,0≤h i)(j): h j ≤ ∑ i,h i:=single_le_sum (fun i _=>H i) (mem_univ j)
  refine ⟨Q,sum_nonneg (fun j _=>h3 _),?_⟩
  filter_upwards [eventually_all.mpr (fun j=> eventually_all.mpr (fun i=>eventually_all.mpr (fun v=>eventually_all.mpr (he j i v))))] with k hK T hT Z hB b y hy hY j i v w
  let D₁ j:= (S.project _).comp (aligned C M k (Z j)); let V:= Order.grid C k b; let g:∀ j:Fin (D+1), C.label j →ₗ[ℂ] (F!).Field j := fun j=> (F!).project j
  let p:= spread S V (D₁ j) (D₁ i) - spread (F!) y (g j) (g i)
  have hV(a:C.label j)(o:C.label i) : p a o=pair S V (D₁ j a) (D₁ i o) - freePair C y a o:=by
     unfold p; simp only [LinearMap.sub_apply]; rw [show spread _ _ _ _ a o=_ from pair_at S V _ _,show spread _ _ _ _ _ _ = _ from pair_at (F!) y _ _];rfl
  change ‖pair S V (D₁ j v) (D₁ i w) - freePair C y v w‖ ≤ _
  rw [← hV]; apply mass_two
  intro a o
  rw [hV]
  exact (hK j i a o T hT Z hB b hy hY).trans (mul_le_mul_of_nonneg_right
    ((show c j i a o ≤ c1 j i a from hX (hc j i a) o).trans <| (show c1 j i a ≤ c2 j i from hX (h1 j i) a).trans ((show c2 j i ≤ c3 j from hX (h2 j) i).trans (show c3 j ≤ Q from hX h3 j))) (Ship.budget_pos ..).le)
end YM.RG12.Arche
