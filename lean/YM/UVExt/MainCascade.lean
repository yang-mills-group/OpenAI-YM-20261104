import YM.UVExt.PowerLimit
/-! Single-history interface (also for comparing two arbitrary histories supported by the same scale receipts). Only the full unmasked leading Taylor-jet system here. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function RG Precision Wilson Lattice Bid Exterior Laurent Bloch Matrix Tree Filter Set Next.Free
open scoped Classical Topology ContDiff BigOperators
set_option maxRecDepth 4000
variable {G:Gauge} {A : Levels G} {P : MapPrices} {M : Horizon A} {s : Supply.Sheet G} {L:Supply.Rolls s} {Q : PostCost L} {H : ChartRatio G} (K : Kin M H)

def jclip (A : Levels G) m := (A.params m).clip
def jrate (A : Levels G) m := (A.params m).width
def jmoney (A : Levels G) m := (A.params m).paths
def jlambda (A : Levels G) m := A.clock.loopCap m
variable (h : Discipline P A M) (hk : K.Planned Q) (m : ℕ) (u : ℕ→ℕ) {U : ℕ→Shadow G}

abbrev woodPassing (K : Kin M H) (u : ℕ→ℕ) m (W : ℕ→Shadow G) := Passing (fun i=>K.path (u i) m) (W m) (jrate A m) (jmoney A m) (jlambda A m) (jclip A m)

variable (hu : Tendsto u atTop atTop) (hU : ∀ m, woodPassing K u m U)
private lemma tensor_symm_limit {E F : Type*} [NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F] {a : ℕ→E→F} {k : ℕ} {A} (h : lucid a) (ht : Tendsto (spray a k) atTop (𝓝 A)) : Tensor.Sym (E:=E) (F:=F) A :=
    fun v t=> tendsto_nhds_unique ((view_cont.tendsto (A,v∘t)).comp (ht.prodMk_nhds tendsto_const_nhds)) (((view_cont.tendsto (A,v)).comp (ht.prodMk_nhds tendsto_const_nhds)).congr' (h.mono fun i hi=> (Analysis.sym_Jet (hi.of_le (finite_cap k)) v t).symm))
include hk hu h
lemma KinHarbor {l x} (hl : Figure P A M l) (hx : ∀ N,m<N → l N m=x) : Harbor A m (A.clock.kernel.penalty) x (fun i=>M.H (u i) m) (fun i=>K.path (u i) m) (jclip A m) := by -- two sides l same use consistency choose per m via blink; need l independent u.
      let hm := hu.eventually (eventually_gt_atTop m); exact ⟨hm.mono fun i hi=>hk.links _ _ hi.le, fun n=>hm.mono fun i hi=> ⟨_,_,h.plan.all _ _ hi.le n⟩, ⟨_,_,P.alpha_pos _,hm.mono fun i hi=>(h.plan.rows _ _ hi.le).2.2.2.1⟩, ⟨u,hu,hm.mono fun i hi=> ((hl.1 _ _ hi.le).inverse.trans (by rw [hx (u i) hi]))⟩,A.clock.kernel.penalty_pos, fun j=> hm.mono fun i hi=>h.symmetry _ _ _ hi⟩

omit h
lemma proc (j) (F : Forest (A.clock.op m j).ratio) (t : (A.clock.op m j).Choices) : Slab F (fun i=>K.path (u i) (m+1)) (fun i=>K.path (u i) m) (jclip A (m+1)) (jclip A m) t
        (fun i=>K.stationary (u i) m j F) (Q.η (A.clock.J (m+1))) (fun i=>selectedMatrix A M (u i) m j) :=
  ⟨(hu.eventually (eventually_gt_atTop m)).mono (fun _ hi=> hk.critical _ _ j hi F|>.1), (hu.eventually (eventually_gt_atTop m)).mono (fun _ hi=>hk.gap _ _ j hi F), (hu.eventually (eventually_gt_atTop m)).mono (fun _ hi=>hk.classicalPart _ m j hi F), (hu.eventually (eventually_gt_atTop m)).mono (fun _ hi=> hk.critical _ _ j hi F|>.2)⟩

omit hk hu
variable (u' : ℕ→ℕ)
def discrepancy {u u'} {X Y} (hU : ∀ m,woodPassing K u m X) (hV : ∀ m,woodPassing K u' m Y) (q) {m p : ℕ} (v : Dir G (A.S.side m p)) := discrep ((Passing.planeTensor (A.S.side m p) q (hU m))) (Passing.planeTensor (A.S.side m p) q (hV m)) v

def confluent (q P : ℕ) := ∀ m, Junction (fun i=> knotted (A.S.side m P) (jclip A m) (K.path (u i) m)) (fun i=>knotted (A.S.side m P) (jclip A m) (K.path (u' i) m)) q

variable {V : ℕ→Shadow G} {t' : ∀ m, Transfers A m} (hUV : ∀ m,woodPassing K u m U) (hV : ∀ m,woodPassing K u' m V)
   (ht : Follows A u M t') (hk' : Tendsto u' atTop atTop) (p : ℕ)
include hUV hV h hk hu hk' ht
lemma joint_two : confluent K u u' 2 p := fun m=>by
   rcases h.figure with ⟨l,hl,hf⟩; obtain ⟨j,hj⟩ := hf m
   have hH {u : ℕ→ℕ} (hp : Tendsto u atTop atTop) : Harbor A m A.clock.kernel.penalty j (fun i=> M.H (u i) m) (fun i=>K.path (u i) m) (jclip A m) := KinHarbor (Q:=Q) K h hk m u hp hl hj
   exact full_basis (hH hu) (hUV m) (hH hk') (hV m) p

-- do not change U or V during induction
set_option maxHeartbeats 500000 in
theorem raiseJoint (q) (hq : q=3∨q=4) (hc : confluent K u u' (q-1) p) : confluent K u u' q p := by
   let C := mapBind A M t'
   let S := fun i=>A.S.side i p
   have hf i := Tree.select (A.clock.op i p).ratio (A.clock.op i p).patch.odd_side
   let F i := Classical.choice (hf i)
   intro m k hkℓ
   by_cases hG : k=q
   · subst k
     have hv (v : Dir G (A.S.side m p)) : discrepancy K (m:=m) (p:=p) hUV hV q v = 0 := by
       let Z := ascender A C m p v
       have hZ : ∀ d:ℕ, discrepancy K (m:=m) (p:=p) hUV hV q v = discrepancy K (m:=m+d) (p:=p) hUV hV q (Z d) := by
          intro d; induction d with
          | zero => rfl
          | succ d ih =>
             exact ih.trans (show _ from Slab.one_floor (proc K hk (m+d) u hu p (F (m+d)) (Classical.arbitrary _)) (proc K hk (m+d) u' hk' p (F (m+d)) (Classical.arbitrary _))
                (hUV (m+d+1)) (hV _) (hUV _) (hV _) hq (hc (m+d+1)) (Q.price _) (Q.price _) (ht.installs (m+d) p) (Z d))
       let D := dCur A C m p v
       let W := fieldFee A C m p v
       obtain ⟨hV',hs,hA⟩ := basic_aid (R:=C) A P m p v (Follows.bottom A M P (u:=u) hu h ht) h.gate
       have hi := true_intercept A m q (boot_cap A m hs hV' q hq) (by omega) p
       let d := discrepancy K (p:=p) (m:=m) hUV hV q v
       suffices hd : ∀ i, |d| ≤ unmaskedInvoice A q (m+i) p (W i) (D i) by
          have hw : (|d|^16:ℝ) ≤ 0 := ge_of_tendsto hi (Eventually.of_forall fun i=>pow_le_pow_left₀ (abs_nonneg d) (hd i) 16)
          by_contra X; have h : (0:ℝ) < |d|^16 := pow_pos (abs_pos.mpr X) _; linarith
       intro i; unfold d; rw [hZ i]; unfold discrepancy discrep
       rw [(hUV (m+i)).mainLimit (S (m+i)) q |>.2,(hV (m+i)).mainLimit .. |>.2]
       obtain ⟨l,hl,hEq⟩ := h.figure; obtain ⟨x,hx'⟩ := hEq (m+i)
       exact upper_residue (l:=x) (KinHarbor K h hk (m+i) u hu hl hx') (hUV _) (KinHarbor K h hk (m+i) u' hk' hl hx') (hV _) (S (m+i)) q hq _ rfl rfl
     have hl := (hUV m).mainLimit (S m) q |>.2
     let f₁ := (hUV m).planeTensor (S m) q
     let f₂ := (hV m).planeTensor (S m) q
     suffices ht : f₁=f₂ by exact ⟨f₁, (hUV m).mainLimit .. |>.1,ht ▸ ((hV m).mainLimit ..).1⟩
     refine Tensor.ext_diag _ _ (tensor_symm_limit ((hUV m).groomed _) ((hUV m).mainLimit (S m) q).1) (tensor_symm_limit ((hV m).groomed _) ((hV m).mainLimit (S m) q).1) ?_ -- expand
     exact funext fun v=> sub_eq_zero.mp (hv v)
   exact hc m _ (by omega)

end YM.UVExt.Paths
