import YM.SignedWilsonExpansion.HighScale
namespace YM.SignedWilsonExpansion.HighRank
set_option autoImplicit false
open Function Filter Set Finset MeasureTheory
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Port MS.Pearl MS.Rake MS.High
open MS.Logarithm MS.Alps MS.Outlook MS.Train MS.Plane.Domain MS.Dock MS.Emit MS.Plane.Flux
open MS.Plane.Wire
open scoped Topology ContDiff BigOperators
open YM.SignedWilsonExpansion.HighScale
noncomputable section
variable {G : Gauge} {d k r : ℕ} {b : Bool} {f : Reading G}
variable (K : Flux (Branch G Axis) FourP ℂ)
lemma tree_height (F H : Law G) (w:Legs (Lane4 G))(b:Bool) (hc: Course b w)
    (gone:∀ (i j : ℕ), i+j=w.length →
      (∀ (w:Legs (Lane4 G)),net w=0 → w.length=i+1 → F w=0) ∨ (∀ (w:Legs (Lane4 G)),Course b w → w.length=j+1 → H w=0)) : tree parity K F H w=0:= by
  unfold tree
  have he: scatter (field (A:=Branch G Axis) parity) w (0:Shared _ ℂ)=0 := map_zero (allocate (field parity) w)
  refine (scatter_congr _ _ _ _ (fun l q hq=>?_)).trans he
  change attaches _ _ _ _ _ _=0
  unfold attaches; dsimp only; rw [neg_neg]
  obtain h|h:= gone l.length q.length (split_length hq)
  · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _=> ?_
    rw [h _ (by simp) (by simp), h _ (by simp) (by simp)]; ring
  have ht (i:Branch G Axis): Course b ((i,net l)::q):=fun t=>by rw [net_cons,split_net hq]; exact hc t
  exact Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> by rw [h _ (ht j) (by simp),h _ (ht i) (by simp)]; ring

lemma cycle_height (μ : Measure FourP) (F : Law G) (w:Legs (Lane4 G))(b:Bool)(hc:Course b w)
    (kill:∀ (v:Legs (Lane4 G)),Course b v→v.length=w.length+2→F v=0): cycle K μ F w=0:=by
  unfold cycle; have he (x:FourP): trc K x F w=0:= by
    rw [at_trc]; refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=>?_
    rw [kill _ (fun h=>by simp [hc h]) (by simp),mul_zero]
  simp_rw [he]; rw [integral_zero]

-- General estimate given joint field height.
structure FlowView (A : Flats G)(P : Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP) (d : ℕ)(b:Bool) (D : Reading G): Prop where
  host : Host A d
  flow (w:Legs (Lane4 G)) (hw : b=true→0<w.length): Track b (four d A) (fun t=> cycle (P.meter t.2) P.measure (four d A t) + D t) (ray w)

lemma FlowView.static {A:Flats G}{P : Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP}{D:Reading G} (H:FlowView A P d b D)(hw:b=true→0<r)
    (hi:∀ t w,Course b w → w.length=r+2 → four d A t w=0)
    (hp:∀ t w,Course b w → w.length=r → D t w=0): Static (four d A) r d b:= by
  refine quiet_static A H.host hw _ (fun w hr=> H.flow w (hr.symm ▸ hw)) ?_
  intro t w hc hr; change cycle _ _ _ w+_=0
  rw [cycle_height _ _ _ w b hc (by rw [hr];exact hi t),hp _ _ hc hr]; simp

lemma FlowView.height {A:Flats G}{P : Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP}{D:Reading G} (H:FlowView A P d b D)
    (bound: ∃ k:ℕ,∀ t, Upper b k (four d A t))
    (sources: ∀ t w,Course b w → d < w.length → D t w=0) : ∀ t, Upper b d (four d A t):= by
  obtain ⟨r,hi⟩:=bound
  suffices ans:∀ k≤r,∀ t (w:Legs (Lane4 G)),Course b w → d<w.length → r < w.length+k → four d A t w=0 by
    intro t w hc hot
    exact ans r le_rfl t w hc hot (by omega)
  intro k; induction k with
  | zero=> intro p t w h _ hk; exact hi t w h (by omega)
  | succ k ih=>
    intro hp t w h ht hh
    exact (H.static (r:=w.length) (fun _=> by omega) (fun t w' h hs=> ih (by omega) t _ h (by omega) (by omega))
      (fun t w' h hs=> sources t w' h (by omega))).over t.1 t.2 w h rfl (by have:=length_pay w; omega)

variable {B : Local.Physical.Deck G} {M : MS.Land.Booked B} (S : MS.Land.MS_Data G M)

local notation "σ" => Archive 4 S.bulk
local notation "Hb" => ((2:ℂ)⁻¹)
lemma bulkView (e : ℕ)(he:1≤e) : FlowView (S.bulk e) (spaceD G) 4 true
    (fun t=> (spaceD G).using_tree e 1 Hb (fun j=>σ j t) (fun j=> σ j t) t.2):=
  ⟨Host.host (gang (S.bulkOK e)),fun w h=> (Outlook.dock S.bulkOK Motif.wisdom).master.road ℝ (ray w) e he (by simpa using h)⟩

lemma bulk_zero : σ 0=0:= by
  ext1 ⟨y,t⟩; change hereZ 4 (S.bulk 0) t y 0=0; rw [(S.bulkOK 0).2 rfl, no0]; rfl
lemma single_off (T:Law G) (b:Bool) (solid:Solid b T 0) (simple:G.Simple) (w:Lane4 G)(h: Course b [w]) : T [w]=0:=by
   rcases w with ⟨⟨a,i⟩,p⟩; apply Landau.single simple (p:=fun i=> T [qnote a i p]); intro u j; exact solid.color [qnote a j p] h u
lemma bulk_single (e:ℕ)(t : Clock ℝ)(w:Lane4 G)(hc : net [w]=0)(simple:G.Simple): σ e t [w]=0:=
  single_off _ true ((Outlook.dock S.bulkOK Motif.wisdom).master.trueC e t) simple w (fun _=> hc)
lemma bulk_first (t:Clock ℝ)(w:Legs (Lane4 G))(hr:1<w.length): σ 1 t w = Motif.B₁ G 0 w:= by
  rw [←Halo.pulse1]; apply sub_eq_zero.mp; exact HB (r:=3) S.bulkOK (Halo.invest G 1) (fun i=> (Halo.fund_one G i).up) 0 w (by omega)
lemma bulk_first_height (t:Clock ℝ)(w:Legs (Lane4 G))(hr:3<w.length): σ 1 t w=0:= by
  rw [bulk_first S t w (by omega),← Halo.pulse1]; exact (Halo.fund_one G 0).up _ (by omega)

abbrev bulkD := σ 2
lemma tree_two(P:Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP) (F:Recount G)(t : Clock ℝ) :
    P.using_tree 2 1 Hb (fun j=>F j t) (fun j=>F j t) t.2=Hb • tree parity (P.meter t.2) (F 1 t) (F 1 t):= by
  unfold using_tree; rw [show paths 2 1={1} by decide, sum_singleton]

lemma bulk_height (t:Clock ℝ) : Upper true 4 (bulkD S t):= by
  apply (bulkView S 2 (by norm_num)).height ((Outlook.dock S.bulkOK Motif.wisdom).master.rank 2) _ t
  intro t w hc hw
  rw [tree_two,Pi.smul_apply,tree_height _ _ _ _ true hc] -- implicit arguments
  · rw [smul_zero]
  intro i j hh; by_cases h:i<3
  · right; intro w _ hj; exact bulk_first_height S _ _ (by omega)
  left; intro w _ hi; exact bulk_first_height S _ _ (by omega)

open MS.Menus MS.Land MS.Mach
open MS.Garment MS.Book
lemma markView (p:Plaid B d) (k:ℕ) :
    FlowView (S.marks d p k) (spaceD G) d false
      (fun t=> (spaceD G).using_tree k 0 1 (fun j=>σ j t) (fun j=> Archive d (S.marks d p) j t) t.2):=
  ⟨Host.host (gang (S.markOK d p k)),fun w _=> (Outlook.roadM S.bulkOK (S.markOK d p)) ℝ (ray w) k (Nat.zero_le _) (fun h=>Bool.noConfusion h)⟩
lemma mark_zero (p:Plaid B 4)(t:Clock ℝ)(w:Legs (Lane4 G))(hp : (Land.read p).grade=2)(hw:1≤w.length):
    Archive 4 (S.marks 4 p) 0 t w=(Land.read p).read w:= by
  have he: Issue 2 ((Motif.Literal.linear (Arts.Mob G)) (M.optics 4 p) 0):=by
    intro m l hl; apply Ele.Top (M.law 4 p) m l; rw [hp, mod_int]; omega
  have ht : Motif.Literal.linear (Arts.Mob G) (M.optics 4 p) 0 0=(Land.read p).read:= (M.law 4 p).2
  rw [←ht]; apply sub_eq_zero.mp; exact HM (r:=2) (S.markOK 4 p) ((M.law 4 p).grows 0) he 0 w (by omega)
lemma mark_zero_rank (p:Plaid B 4)(t:Clock ℝ)(w:Legs (Lane4 G))(hp : (Land.read p).grade=2)(hw: w.length≠2)(hv:1≤w.length):
    Archive 4 (S.marks 4 p) 0 t w=0:= by
  rw [mark_zero S p t w hp hv,← (M.law 4 p).2]; apply Ele.Top (M.law 4 p) 0 w; rw [hp, mod_int]; omega


abbrev ear (p : Plaid B 4) := Archive 4 (S.marks 4 p)

lemma mark_sphere (p : Plaid B d) : Disc false 0 σ (Archive d (S.marks d p)) 1 d :=
  Outlook.fieldD S.bulkOK (S.markOK d p) Motif.wisdom ((M.law d p).moodQ)

local notation "Tx" => spaceD G

lemma tree_first (P:Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP) (F H:Recount G)(t:Clock ℝ) :
    P.using_tree 1 0 1 (fun j=>F j t) (fun j=>H j t) t.2 = tree parity (P.meter t.2) (F 1 t) (H 0 t) := by
  unfold using_tree; rw [show paths 1 0={0} by decide,sum_singleton,one_smul]
lemma tree_second (P:Domain (parity (C:=G.ColorIndex) (A:=Axis)) FourP) (F H:Recount G)(t:Clock ℝ) :
    P.using_tree 2 0 1 (fun j=>F j t) (fun j=>H j t) t.2 = tree parity (P.meter t.2) (F 2 t) (H 0 t) + tree parity (P.meter t.2) (F 1 t) (H 1 t) := by
  unfold using_tree; rw [show paths 2 0={0,1} by decide, sum_insert (by simp),sum_singleton,one_smul]

variable (p : Plaid B 4)(t : Clock ℝ)(hp : (Land.read p).grade=2)
include hp
private lemma tree_mark_one (K:Flux (Branch G Axis) FourP ℂ) (w:Legs (Lane4 G))(hm:3 < w.length) :
    tree parity K (σ 1 t) (ear S p 0 t) w=0 := by
  apply tree_height _ _ _ _ false (fun h=>Bool.noConfusion h)
  intro i j hw; by_cases hj:j≤1
  · left; intro w' _ hn; exact bulk_first_height S _ _ (by omega)
  right; intro w' _ hn; exact mark_zero_rank S p t w' hp (by omega) (by omega)
lemma mark_one_4 : Upper false 4 (ear S p 1 t):= by
  refine (markView S p 1).height ((mark_sphere S p).master.rank 1) ?_ t
  intro t w _ hw
  rw [tree_first]; exact tree_mark_one S p _ hp _ w (by omega)
lemma mark_one_top : Static (ear S p 1) 4 4 false := (markView S p 1).static (fun h=>Bool.noConfusion h)
   (fun t w hc hr => mark_one_4 S p t hp w hc (by omega)) (fun t w hc hr => by rw [tree_first]; exact tree_mark_one S p t hp _ w (by omega))
lemma mark_first_four_q (w:Legs (Lane4 G))(hr:w.length=4) : natQ (ear S p 1 t) w=0:= by
  let P:= degreeMaster id (spaceD G)
  unfold natQ; rw [(mark_sphere S p).master.qfm 1 t w (by omega) (fun h=>Bool.noConfusion h) (fun h=>Bool.noConfusion h)]
  unfold Ward recu; simp only [Pi.neg_apply,Pi.add_apply,tree_first]
  rw [cycle_height _ _ _ _ false (fun h=>Bool.noConfusion h) (fun v hc hv=> mark_one_4 S p t hp _ hc (by omega)), tree_mark_one S p t hp _ w (by omega)]; simp
open Landau.Detect.Mark
omit hp in
lemma flat_spins_static {d:ℤ} {b:Bool}{f: Reading G} (F: Static f r d b)
    (w L:Legs (Lane4 G))(hw:Course b w)(hl:Course b L)(hg:w.length=r)(hd:fieldDim wfield w=d)
    (he:w.map Prod.fst=L.map Prod.fst): f t w=f t L:= by
  let Z:Lane4 G→Lane4 G := fun v => (v.1,0)
  have hb: L.length = r:= by simpa [hg] using congr_arg List.length he.symm
  have hs: fieldDim wfield L=d:= by unfold fieldDim; rw [← List.map_map,←he, List.map_map]; exact hd
  have val (w:Legs (Lane4 G))(hc:Course b w)(hr:w.length=r)(hd:fieldDim wfield w=d): f t w=f t (w.map Z):= by
    have hu := F.form t.1 t.2 (ray w) (ray_course hc) ((ray_len w).trans hr)
    rw [ray_dim, hd,sub_self] at hu
    have ht:= shape_constant hu 1
    simp only [fieldVal,ray_sail] at ht
    rw [ht]; congr; simp [sail,ray,Z]
  rw [val w hw hg hd, val L hl hb hs]
  apply congr_arg
  convert congr_arg (List.map (fun i=>(i,(0:FourP)))) he using 1 <;> simp [Z]

lemma mark_first_quartic (X:Legs (Lane4 G))(hl:X.length=4): ear S p 1 t X=0:= by
  let F:= ear S p 1
  have ht:Static F 4 4 false:= mark_one_top S p hp
  have core(w:Legs (Lane4 G)):Course false w:=fun h=>Bool.noConfusion h
  let m:=fieldDim wfield X
  rcases lt_or_ge 4 m with hi|hi
  · exact ht.over t.1 t.2 X (core _) hl hi
  have hh:=length_pay X
  have cost:fieldDim wfield X=4:=by dsimp only [m] at *; omega
  by_cases e:fieldDim ghostNo X=0
  swap; · exact ((mark_sphere S p).master.trueC 1 t).ghost X (core _) e
  have all:=(pay_eq X (by rw [hl,cost]; rfl))
  have hX:∀i∈X,∃ a k p,i=W a k p:= fun i hi=> cost_vec i (all i hi) (no_eq X all e i hi)
  obtain ⟨x,y,z,u,rfl⟩:= List.length_eq_four.mp hl
  rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons] at hX
  obtain ⟨⟨a,i,q,rfl⟩,⟨b,j,P,rfl⟩,⟨c,k,Q,rfl⟩,⟨d,l,T,rfl⟩,_⟩:=hX
  let v := spike a
  have Wd:= mark_first_four_q S p t hp [C i v, W b j 0,W c k 0, W d l 0] rfl
  rw [qGhost, qAA,qAA,qAA,q0] at Wd
  have hv x y: precision x y (0:Momentum Axis)=0:=by unfold precision delta Momentum.sq; simp
  simp only [hv, Complex.ofReal_zero,neg_zero,zero_mul,Finset.sum_const_zero,add_zero,sub_zero] at Wd
  rw [Finset.sum_eq_single a (fun j _ hj=>by simp [v,hj]) (by simp)] at Wd
  change F t _=0
  rw [flat_spins_static t ht _ [W a i v, W b j 0,W c k 0,W d l 0] (core _) (core _) hl cost (by rfl)]
  simpa [v,F] using Wd

lemma mark_one_height : Upper false 3 (ear S p 1 t):= by
  intro w hc hm
  rcases lt_or_eq_of_le (show 4≤w.length from by omega) with h|h
  · exact mark_one_4 S p t hp w hc h
  exact mark_first_quartic S p t hp w h.symm
lemma mark_two_height : Upper false 4 (ear S p 2 t):= by
  refine (markView S p 2).height ((mark_sphere S p).master.rank 2) ?_ t
  intro t w hc hr
  rw [tree_second,Pi.add_apply,tree_height _ _ _ _ false hc,tree_height _ _ _ _ false hc,add_zero]
  · intro i j h; by_cases hj:j ≤ 2
    · left; intro w _ hn; exact bulk_first_height S t w (by omega)
    right; intro w hw hn; exact mark_one_height S p t hp w hw (by omega)
  intro i j h; by_cases hj:j ≤ 1
  · left; intro w he hn; exact bulk_height S t w (fun _=>he) (by omega)
  right; intro w _ hn; exact mark_zero_rank S p t _ hp (by omega) (by omega)

end
end YM.SignedWilsonExpansion.HighRank
