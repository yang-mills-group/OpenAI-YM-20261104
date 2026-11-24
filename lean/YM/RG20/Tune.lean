import YM.RG20.Flight
/-!
# Orbit, projection and cone for the reserve transmission
Source adapted from UVExtension/Lacing/{Loads,Reprise}.lean; see also OPE/Vitrines/{Care,Step}.lean. Re-specialize and re-check against
the UV Rama (Rainfall/Lacing) data; no identification of independent witnesses. See ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open Eyelet MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "Λ"=> Real.sqrt (H.levels.clock.forcedAllowance m)
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "n"=> H.S.side m p
local notation "n'"=> H.S.side (m+1) p
local notation "Old"=> H.rep N p (m+1)
set_option quotPrecheck false
local notation "R"=> H.rep N p m
local notation "O" => Bucket F (R).p A n
set_option quotPrecheck false
private lemma foam20 {ι WW : Type*} {u : WW → ℂ} {f : ι → WW → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h; obtain ⟨c,hh⟩ := hv
  refine ⟨_,hb.mul_left c,fun i x => ?_⟩
  rw [norm_mul]; exact mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
theorem burden20 (Z : Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (P : Coefficient F (H.S.side (m+1) p))(X:Set Wing)(D:GaugeDoor Old R)(L0:Lacing.Fence (F:=F) H N p m A) (i:Option F.Index)
    (h:Vintage.YM.RG.History.Selected H)(hm:m<N)(hp:P.Format 0 A (H.rep N p (m+1)))(hP:P.remBound 0 (H.rep N p (m+1)) κ t)(hx:P.x=Lacing.seed F i)
    (hz:0≤η)(hD:Manor20 B H N p m A Z D X L0 T C η w) (hK: κ ≤1):
    let L := H.S.block m; let x:= P.x
    Sends20 B H N p m A D X (P.exponentialEntry 0 B (Old)) (profile (Old).activities P.forced) (P.x 0) (P.density 0 B Old) (T.leads L x) (η*(F.coeffSize (F.core x)+t)) (C*F.coeffSize (vowel F L (F.core x))+η*t) (peat (F:=F) w i+2*t) (L0.rain (Eye P A Old κ).2 i) :=by
   intro L x
   have HP:Eligible P A Old κ:=⟨⟨Z⟩,hp,_,hP⟩
   let Q:= ageing P Z; have hx':Q.x=x:=rfl; have htQ: Q.Format 0 A Old:=dye P Z hp; have hw: Q.remBound 0 Old κ t:= priced P Z hp.origin hP
   have hr: profile (Old).activities Q.forced=profile (Old).activities P.forced:= stows Z P
   have he: Q.exponentialEntry 0 B (Old)=P.exponentialEntry 0 B (Old):=respect P Z hp.origin B
   let J:=Extra.Histories.primary (0:Site (H.S.side (m+1) p)) x
   let f:= consist (J.density 0 B (Old)) (fun i => Extra.Histories.salary (Old) (Q.support i) (Q.regular i)) (fun i => Extra.Histories.fare (Old) i (Q.forced i))
   have hk := (h.represents N p (m+1) hm).good
   have h0 : 0 < κ := Real.sqrt_pos.2 (forcedPos ..)
   have hE := Rep.envelope Old hk
   have hR := (Rep.exponentEnv Old hk).exp
   have hL := rem_dominated hw
   have hy := Coefficient.envelope B hk (primary_rem (o:=0) x h0) (primary_format (o:=0) (H:=A) x); let U₀:= Old
   have hu : Dominated f := by
      refine InputColumn.dominated hy.cost (foam20 (Q.regular_series hw) ?_) (foam20 (dress_abs hk hL) ?_)
      · obtain ⟨c,hc⟩ := hE.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
      obtain ⟨c,hc⟩ := hR.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
   have hf (i : Listing) : Measurable (f i) := by
      rcases i with i|i|i; exact hy.meas
      exact (Complex.continuous_ofReal.measurable.comp hE.meas).mul (masked_measurable _ _ _ (htQ.smooth i).borel)
      exact (Complex.continuous_ofReal.measurable.comp hR.meas).mul ((htQ.borel i).mul (dressed_meas hk i))
   have hP': P.density 0 B Old=Q.density 0 B Old:= reentry he.symm hk (rem_dominated hP) hL hr.symm
   have hW : Q.density 0 B Old = fun U => ∑' i, f i U := by
      funext U; let a i := Q.maskedTerm Old i U; let b i := Q.forced i U * dressed Old i U
      have hn : HasSum a (∑' i, a i) := ((Q.regular_series hw).summable U).hasSum
      have ha : HasSum b (∑' i, b i) := ((dress_abs hk hL).summable U).hasSum
      rw [(added (f:=fun i => f i U) (hn.mul_left ((Old).eval U:ℂ)) (ha.mul_left (Real.exp ((Old).exponent U):ℂ))).tsum_eq]; change _ = (Extra.Histories.primary 0 x).density 0 B Old U + _
      rw [primary_density,Coefficient.density,dress_eq hk hL]; change ((Old).eval U:ℂ)*(part B 0 Old U Q.x+∑' i,a i) + _ = _; rw [hx']; unfold b; ring

   obtain ⟨l,r,ha,hb,hS,-,⟨a,hA,hA'⟩,b,hB,hB'⟩:=hw
   let g i:=(Old).p.mass (Q.support i) (a i); let k i:=((Old).p.mass ((Old).activities.forced i).support (b i))/κ
   let y:= F.coeffSize (F.core x); let d':= F.coeffSize (vowel F L (F.core x))
   let V:= consist (η*y) (fun i=> η*g i) (fun i=> η*k i); let W:= consist (C*d') (fun i=> η*g i) (fun i=> η*k i)
   let U': Listing→F.Coeff:= consist (T.leads L x) 0 0
   have Hk:SumBudget k r:=by
      refine ⟨fun i=>div_nonneg (hB.1 _) h0.le,hB.2.1.div_const _,?_⟩; unfold k; rw [tsum_div_const]; exact (div_le_iff₀ h0).2 (hB.2.2.trans_eq (mul_comm ..))
   let Hp := consist (peat (F:=F) w i) (fun i=> 2*g i) (fun i=>2*k i); let O':Listing → Config G (H.S.side (m+1) p)→ℂ:=consist (J.exponentialEntry 0 B Old) (Q.maskedTerm Old) (fun _=>0); let E':= consist 0 (fun _=>0) (fun i=> exactGas U₀.activities i (Q.forced i)); let Y': Listing→ℂ:= consist (P.x 0) 0 0
   let yg:= L0.income (Eye P A Old κ).2 i
   have hin(i':Listing): Sends20 B H N p m A D X (O' i') (E' i') (Y' i') (f i') (U' i') (V i') (W i') (Hp i') (yg i'):=by
      rcases i' with i'|j|j
      · change Sends20 _ _ _ _ _ _ _ _ ((Extra.Histories.primary 0 P.x).exponentialEntry 0 B Old) 0 (P.x 0) ((Extra.Histories.primary 0 P.x).density 0 B Old) (T.leads L P.x) (η*F.coeffSize (F.core P.x)) (C*F.coeffSize (vowel F L (F.core P.x))) (peat (F:=F) w i) (L0.vane i)
        -- dependent read technique
        erw [hx]; exact hD.pivot i
      · let he:= key n' j; let r:= HP.fernP he
        have hm : yg (Sum.inr (.inl j))= L0.glass he ((↑(Eyelet.fee (Old).p he.1.val):ℂ) • twig _ r):=by unfold yg;rw [HP.vistas];rfl
        rw [hm]; exact hD.glass he r (a j) (hA' j)
      by_cases Ho:j∈Set.range (L0.route); swap
      · let Y:= Q.forced j; change Sends20 B H N p m A _ _ 0 (exactGas _ j Y) 0 (Extra.Histories.fare _ j Y) 0 (η*k j) (η*k j) (2*k j) (yg _)
        have hr : Y=0:= pit Z P (hD.route ▸ Ho)
        rw [hr]; rw [show exactGas (Old).activities j 0=0 by simp [exactGas]]; rw [show Extra.Histories.fare Old j 0=0 from funext fun U=> by simp [Extra.Histories.fare]]; rw [show yg (.inr (.inr j))=0 from by unfold yg; rw [HP.vistas]; exact extend_apply' (fun u=> L0.wing u (HP.tollK u)) (0:ℕ→ Bucket F (R).p A n) _ Ho]
        exact leisure20 B _ _ _ _ _ X D (mul_nonneg hz (Hk.1 j)) (mul_nonneg zero_le_two (Hk.1 j))
      obtain ⟨u,rfl⟩:=Ho; let j:=L0.route u; have he:j=cart Z u:=congr_arg (fun f:StockTag n'↪ℕ=> f u) hD.route
      let Zu:= HP.sapP u; have hy: Q.forced j=Zu.val:=he ▸ stowed Z P u
      have hHp : (Old).p.mass u.val.1 (b j)= (Old).p.mass ((Old).activities.forced j).support (b j):=by
          apply congr_arg (fun x=> (Old).p.mass x (b j)); rw [he]; exact (Z.support (u,0)).symm
      have Q':=hD.wing u Zu (b j) (hB' j|>.1) (hy ▸ (hB' j).2)
      have hh:yg (.inr (.inr j))=L0.wing u (HP.tollK u):= by unfold yg; rw [HP.vistas]; exact L0.route.injective.extend_apply (fun t=>L0.wing t (HP.tollK t)) 0 _ -- may need explicit
      change Sends20 _ _ _ _ _ _ _ _ 0 (exactGas _ j (Q.forced j)) 0 (Extra.Histories.fare _ j (Q.forced j)) 0 _ _ (2*k j) _; rw [hy,hh]
      rw [hHp] at Q'; exact rents20 _ _ _ _ _ _ D X _ Q' le_rfl le_rfl (mul_le_mul_of_nonneg_left (le_div_self (hB.1 j) h0 hK) zero_le_two)
   let z':=(∑' i,g i)+(∑' i,k i); have hy':z'≤t:=(add_le_add hA.2.2 Hk.2.2).trans hS
   have hV:HasSum V (η*y+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have hW':HasSum W (C*d'+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have hQ:HasSum Hp (peat (F:=F) w i+2*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (Hk.2.1.hasSum.mul_left _)
   have huP : HasSum U' (T.leads L x):=by simpa only [U',consist,add_zero, Sum.elim_inl] using added (f:=U') hasSum_zero hasSum_zero
   have hP₀: Summable (fun i=> F.coeffSize (U' i)):= by apply summable_of_ne_finset_zero (s:={Sum.inl ()}); rintro (⟨⟩|i|i) hi; simp at hi; all_goals simp [U',Labels.Frame.coeffSize,consist]
   have hδ : HasSum Y' (P.x 0):=by simpa only [Y',consist,add_zero, Sum.elim_inl] using added (f:=Y') hasSum_zero hasSum_zero
   have he' (U): HasSum (fun j=> O' j U) (P.exponentialEntry 0 B Old U):=by
      have hJ j:J.maskedTerm Old j U=0:=congr_fun (map_zero (Push.Local.maskLinear _ _)) _
      have Hx(i:Coefficient F (H.S.side (m+1) p)):i.exponentialEntry 0 B Old U= part B 0 Old U (Coefficient.x i)+∑' j,i.maskedTerm Old j U:=rfl
      rw [← he,Hx,hx']; convert added (f:=fun j=> O' j U) ((Q.regular_series (priced P Z hp.origin hP)).summable U|>.hasSum) (hasSum_zero) using 1; change _= J.exponentialEntry _ _ _ U+(_+0);rw [Hx]; simp_rw [hJ,tsum_zero,add_zero];rfl -- hw consumed use
   have hq' j U: HasSum (fun i=> E' i j U) (profile (Old).activities P.forced j U):=by
      rw [← hr]; convert added (f:=fun i=>E' i j U) hasSum_zero (profiled (Old).activities _ hL U j) using 1; change _=(0:ℂ)+(0+_); rw [zero_add,zero_add]
   have h' := vouchers20 B H N p m A D hD.good h hm.le hD.coins (L0.income (Eye P A Old κ).2 i) hin he' hq' hδ hu hf hP₀ hV.summable hW'.summable hQ.summable
   rw [← hW,← hP',hV.tsum_eq, hW'.tsum_eq,hQ.tsum_eq,huP.tsum_eq] at h'; exact rents20 B H N p m A D X _ h' (by rw [mul_add η (F.coeffSize (F.core P.x)) t]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' zero_le_two))
end YM.UVExtension.Lacing

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Eyelet MergeProof
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Extra.Histories Motion PhysicalNext.Repeat Lotus
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G)

variable (W: Worth)
omit A in
private theorem blast_march20 (m : ℕ) {f : F.Coeff → Config G (H.S.side (m+1) p) → ℂ} (h : IsLinearMap ℂ f)
    (hF : ∀ v, Integrable (f v) (prior G _)) : IsLinearMap ℂ fun x => blast H N p m d (f x) := by
  constructor
  · intro x y
    simp only [blast,h.map_add,StepData.push_add (H.levels.transition_mass ..) _ _ (hF _) (hF _),smul_add]
  intro c y
  simp only [blast,h.map_smul,StepData.push_smul _ _ _ _ (hF _), smul_comm c]


set_option maxRecDepth 4000 in
set_option maxHeartbeats 960000 in
set_option synthInstance.maxHeartbeats 160000 in
theorem repriseQ20 (m : ℕ) (V : Voice F H p (m+1)) {η C : ℝ}
    (h : Vintage.YM.RG.History.Selected H) (hm : m<N) (hq : Heard B H N p A (m+1) V) (hw : roomCost H.levels W)
    (hb : Bank W H.levels) (T : Heading F)
    (D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
    (Xk : Set Wing){t : ℝ}(hxt:0≤t)(hk:Set.Finite Xk)
    (κk: Real.sqrt (H.levels.clock.forcedAllowance (m+1))≤1)(he : Buys H F W m C η)
    (K:Planned.GuardedAtom.Guard.Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities) (L0:Fence (F:=F) H N p m A)
    (ht: Manor20 B H N p m A K D Xk L0 T C η t) (hr : Chorus H N p (m+1) V)(hT:B.Sound A)(hN:∀ U,(H.rep N p (m+1)).eval U ≠ 0):
    ∃ Q : Voice F H p m, Heard B H N p A m Q ∧ Responds B H N p W m V Q ∧ Chorus H N p m Q∧
       (∀ x:F.Coeff, Face H N p A m Q x = Lacing.load H N p A m L0 V (V.index x)) ∧
       (∀ x:F.Coeff, Blown (Q.plays x) 0 (H.rep N p m) (Q.charge x)) ∧
       Carol B H N p m D V Q t := by
  classical
  let L:= H.S.block m
  have hD:=ht.good
  let f (v) := (V.plays v).density 0 B (H.rep N p (m+1))
  have hf (v) : Integrable (f v) (prior G _) :=
    Vintage.YM.Extra.Histories.play_integrable H N h hm (hq.earns v).1 (hq.earns v).2
  let P := fun x => blast H N p m d (f x)
  have hP : IsLinearMap ℂ P := blast_march20 H N p m hq.values hf
  have hM (v) (y) : dance y (P v) = P (Motion.patch F y v) := by
    rw [← show blast H N p m d (dance y (f v))= dance y (P v) from blast_dance H N p m d y (f v) (hf v)]
    rw [show dance y (f v) = f (Motion.patch F y v) from hq.travels ..]

  let s := (H.levels.params (m+1)).columns

  let R := H.rep N p m
  let Dm (z) := F.coeffSize (vowel F L (F.core z))
  let c := C + η*s
  let ε := η*(1+s)
  have hS : 1 ≤ s := (H.levels.params (m+1)).columns_ge
  have hη := he.epsilon
  have hc' := he.cost
  have hs : 0 ≤ s := by linarith
  have hcc : C ≤ c := le_add_of_nonneg_right (by positivity)
  have hc : 0 ≤ c := by linarith
  have hε : 0≤ε := by unfold ε; positivity
  let J := Size.axis F
  let j i:= V.index.symm (J i)
  let Pm i:= V.plays (j i);let E:=H.rep N p (m+1); let x' :=s
  have hv i: V.index (j i)=J i:= V.index.apply_symm_apply _
  have hxC i:(Pm i).x=J i:=(hq.currents _).trans (hv i)
  have hd' (i : F.Index) : Sends20 B H N p m A D Xk ((Pm i).exponentialEntry 0 B E) (profile E.activities (Pm i).forced) (J i 0) (f (j i)) (T.leads L (J i))
      (ε * F.coeffSize (F.core (J i))) (c*Dm (J i)) (t+2*s) (L0.rain (Eye (Pm i) A E (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))).2 (some i)):=by
    let v := V.index.symm (J i)
    have hh : V.index v = J i := V.index.apply_symm_apply _
    have h := burden20 B H N p m A K (Pm i) Xk D L0 (some i) h hm (hq.earns _|>.1) (hq.earns _|>.2) (hxC i) hη ht κk
    change Sends20 _ _ _ _ _ _ _ _ _ _ ((Pm i).x _) _ (T.leads L ((Pm i).x)) (η * (F.coeffSize (F.core (Pm i).x)+V.charge v)) (C*Dm (Pm i).x+η*V.charge v) (peat (F:=F) t (some i)+2*V.charge v) _ at h -- let. maybe need dsimp
    rw [hxC] at h
    have hu : V.charge v ≤ s * F.coeffSize (F.core (J i)) := hh ▸ hq.cone v
    have hz : F.coeffSize (F.core (J i)) ≤ Dm (J i) := (Work.G08.size_vowel F L _).1
    refine rents20 _ _ _ _ _ _ D Xk _ h ?_ ?_ (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hu.trans ?_) zero_le_two))
    · exact (mul_le_mul_of_nonneg_left (add_le_add_right hu _) hη).trans_eq (by unfold ε J; ring)
    · exact (add_le_add_right (mul_le_mul_of_nonneg_left (le_trans hu (mul_le_mul_of_nonneg_left hz hs)) hη) _).trans_eq
        (by unfold c Dm L J; ring)
    apply mul_le_of_le_one_right hs; unfold J;rw [Size.core_axis];split; next h=> simp [Frame.coeffSize]
    next h=> rw [Size.size_axis]
  choose Z₀ h₀ hβ hSnow heF using fun i=> (hd' i).mints
  let X i:= (Z₀ i).x
  let Fm (m':Motion) : E.activities.Moves m'.1 ((H.levels.clock.op _ p).ratio.embed 0):= (h.represents N p (m+1) hm).good.labels.moves _ _|>.some
  let u₀ (m':Motion): R.activities.Moves m'.1 0:= (h.represents N p _ hm.le).good.labels.moves _ _|>.some
  let Q i m:= Planned.GuardedAtom.audition (u₀ m) (Z₀ i)
  let y₀ := Real.sqrt (H.levels.clock.forcedAllowance m)
  have HX(i m'): F.coeffSize (Motion.patch F m' (X i)- Motion.patch F m' (T.leads L (J i)))≤ε * F.coeffSize (F.core (J i)):= by rw [← Planned.GuardedAtom.patch_sub]; exact (patch_cost _ _ _).trans (h₀ _).leadP
  have hi(i m'): (Q i m').x=Motion.patch F m' (X i) ∧ (Q i m').Format 0 A R ∧ (Q i m').remBound 0 R y₀ (c*Dm (J i)) ∧ (Q i m').density 0 B R=dance m' (P (j i)):=by
     obtain ⟨a,b,hq,hF⟩:=(h₀ i).future
     obtain ⟨hz,hx,hP,hβ⟩:= Planned.GuardedAtom.audition_receipt m' (u₀ m') ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p)) hT (h₀ i).format hq
     exact ⟨hz,hx,hP.bound hF,hβ.trans (congr_arg (dance m') (h₀ _).agrees)⟩
  have hF i m':= (hi i m').2.1; have hY i m':= (hi i m').2.2.1; have hQ i m':= (hi i m').1; have hU i m':= (hi i m').2.2.2
  let O : Tally F → Coefficient F _ := fun j => Q j.2 j.1
  let Y : F.Coeff →ₗ[ℂ] Tally F → ℂ := (chips F).comp V.index.toLinearMap
  let Z : F.Coeff → Coefficient F _ := pencil (code (Tally F)) O Y
  let a v := c * orbitCost F * Dm (V.index v)
  let y := Real.sqrt (H.levels.clock.forcedAllowance m)
  have hy : 0<y := Real.sqrt_pos.2 (forcedPos ..)
  have hy' := (h.represents N p m hm.le).good
  have hb' (v) : (Z v).Format 0 A R ∧ (Z v).remBound 0 R y (a v) := by
    let t (j : Tally F) := c*Dm (J j.2)
    have h := pencil_cost (code _) O Y (X:=t) hy (fun j => ⟨hF j.2 j.1,hY j.2 j.1⟩) v
    exact ⟨h.1,rem_mono h.2 (residual_bill F L c hc (V.index v))⟩
  have hZ (v) : (Z v).x = repaint F X (V.index v) := by
    unfold Z
    rw [pencil_x]
    exact Finset.sum_congr rfl fun i _ => congr_arg (chips F (V.index v) i • ·) (hQ ..)
  have hp (v) : (Z v).density 0 B R=P v := by
    let K := (IsLinearMap.mk' P hP).comp V.index.symm.toLinearMap
    have hh (v) (y) : dance y (K v)=K (Motion.patch F y v) := by
      change dance y (P _)=P _
      rw [hM]; apply congr_arg
      apply V.index.injective; rw [← hq.moves]; simp
    funext x
    have hi := field_same F K hh (V.index v) x
    unfold Z
    rw [pencil_density (code _) O Y hy' hy (X:=fun j => c*Dm (J j.2)) (fun j => hY j.2 j.1)]
    refine (Finset.sum_congr rfl (g:=fun i : Tally F => chips F (V.index v) i *
        dance i.1 (K (J i.2)) x) fun i _ => ?_).trans (hi.trans ?_)
    · exact congr_arg ((Y v i) * ·) (congr_fun (hU i.2 i.1) x)
    change P (V.index.symm (V.index v)) x= P v x; rw [LinearEquiv.symm_apply_apply]

  have hI (v) : F.coeffSize ((Z v).x - T.leads L (V.index v)) ≤
      barunit L * F.coeffSize (F.core (V.index v)) := calc
    _ ≤ ε*orbitCost F*F.coeffSize (F.core (V.index v)) := by
      rw [hZ]; exact budgets_orbit F L T X (V.index v) ε hε (fun i => HX i.2 i.1)
    _ ≤ _ := mul_le_mul_of_nonneg_right he.tiny (Work.G08.size_nonneg ..)
  have ht' (v) : direction H W m F (Z v).x (V.plays v).x (a v) (V.charge v) := by
    rw [hq.currents]
    have ho : 0 ≤ V.charge v := rem_nonneg (hq.earns v).2
    have hg : 0 ≤ barunit L := by
      have hl : (0 : ℝ) ≤ L.val := by positivity
      unfold barunit puffs; positivity
    refine ⟨rem_nonneg (hb' v).2,ho,T.map,fun x => ?_, (hI v).trans ?_,?_⟩
    · have hb : C ≤ W.K (H.levels.clock.J (m+1)) :=
        le_trans (hcc.trans (le_mul_of_one_le_right hc (orbitCost_one_le F))) he.funds
      have hz := mul_le_mul_of_nonneg_right hb (Work.G08.size_nonneg F x)
      exact ⟨((ht.map_norm x).1).trans hz,((ht.map_norm x).2).trans hz,(T.core_comm x).symm⟩
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ho) hg
    change c * orbitCost F * Dm (V.index v) ≤ _
    refine le_trans (mul_le_mul_of_nonneg_right he.funds (Work.G08.size_nonneg F _)) ?_
    change _*Dm _ ≤ _*F.coeffSize (F.core (vowel F L _))+_
    rw [Work.G08.core_vowel]
    exact le_add_of_nonneg_right (mul_nonneg hg ho)

  have hback (v) := Work.G08.cone_step W H hw hb m F _ _ _ _ (ht' v) (show V.charge v ≤
    s * F.coeffSize (F.core (V.plays v).x) from (hq.currents v).symm ▸ hq.cone v)
  have hBook : Ledger F _ Z := pencil_ledger ..
  let Ψ := IsLinearMap.mk' _ hBook.x
  have hΨ : Injective Ψ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have ha := (hback v).2.1
    rw [show (Z v).x=0 from hv, hq.currents] at ha
    apply V.index.injective
    rw [map_zero]
    exact Work.G08.size_separates F _ (by simpa [Frame.coeffSize] using ha)
  let out : Voice F H p m := ⟨Z,a,LinearEquiv.ofBijective Ψ ⟨hΨ, LinearMap.injective_iff_surjective.mp hΨ⟩⟩
  let M₀(v) := profile R.activities (Z v).forced
  have hMx(v): M₀ v= ∑ j:Tally F,Y v j • floatUp j.1 0 (profile R.activities (Z₀ j.2).forced):=by
      funext p' U; have h:= profile_merge (code _) (fun j:Tally F=> (Extra.Histories.stretch (Y v j) (Q j.2 j.1))) hy (fun j=> stretch_rem _ (hY j.2 j.1)) Summable.of_finite p' U
      rw [show M₀ v p' U= _ from h.tsum_eq.symm,tsum_fintype]; simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i _=> congr_fun (congr_fun ((profile_scale ..).trans (congr_arg (fun p=>(Y v i) • p) (foyer i.1 0 (u₀ i.1) (Z₀ i.2)))) _) _)
  -- union dependent turning (no accidental O push reuse)
  let X': Set Wing:= ⋃ i:Motion,(Wing.labelRoute (Fm i)) '' Xk
  have hhQ(z:Tally F): let T':= V.index.symm (Motion.patch F z.1 (J z.2)); let U:=V.plays T'; Tale X' 0 0 ((↑L.val:ℂ)^d) (U.exponentialEntry 0 B E) (profile E.activities U.forced) (profile R.activities (O z).forced) ((Motion.patch F z.1 (J z.2)) 0) (t+2*s) (c*Dm (J z.2)) D:=by
     intro T' U; let i:=z.2; let m':=z.1; let V':Site (H.S.side (m+1) p):= (H.levels.clock.op m p).ratio.embed 0
     have he: V'= 0:= Motion.embed_origin _
     have hAA: X'≥ (Wing.labelRoute (Fm z.1)) '' Xk:=subset_iUnion (fun i:Motion=> (Wing.labelRoute (Fm i)) '' Xk) z.1
     have hmV:T'=Motion.patch F z.1 (j z.2):= V.index.injective (by rw [← hq.moves]; change V.index (V.index.symm _)= _;simp [j])
     have hW:= (hβ i).gain hD z.1 0 (Fm z.1) (by unfold Motion.scalar;split<;>simp)
     have hp := hW.climb hAA le_rfl le_rfl
     rw [show U= V.plays (Motion.patch F z.1 (j z.2)) from congr_arg _ hmV]
     rw [← hr.pages, show profile R.activities (O z).forced = _ from foyer z.1 0 (u₀ z.1) (Z₀ z.2), ← Vintage.YM.MergeProof.chanting B H N p _ A V hT hq hr h hm hN] -- want profile O z = floatUp z
     rw [show (H.levels.clock.op _ p).ratio.embed 0=0 from he] at hp -- might Motive if Fm? X' reducible
     simp only [affine,Signed.act_zero,zero_add] at hp
     rw [show Motion.patch F z.1 (J _) 0 = scalar z.1 (J i 0) from ?_]; exact hp
     unfold Motion.patch scalar; split <;>simp only [Pi.star_apply, Push.Local.act_at_zero] <;> rfl
  refine ⟨out, ⟨hBook,hb',fun _ => rfl,fun v => (hback v).1,?_,fun v x => ?_,?_, ?_, ?_⟩,⟨hp,ht'⟩,?_,?_,?_ ,?_⟩
  · intro i j
    change a (i+j) ≤ a i + a j
    unfold a Dm
    rw [map_add,map_add,← mul_add,show vowel F L (F.core (V.index i) + F.core (V.index j)) =
      vowel F L (F.core (V.index i))+vowel F L (F.core (V.index j)) from by ext; simp [vowel,mul_add]]
    exact mul_le_mul_of_nonneg_left (Size.add F _ _) (mul_nonneg hc (zero_le_one.trans (orbitCost_one_le _)))
  · change Motion.patch F x (Z v).x=(Z _).x
    rw [hZ,hZ,repainted_eq,hq.moves]
  · change (Z (unitVec F H N)).x = _
    have hc := hI (unitVec F H N)
    rw [hq.unit,show F.core (unitVec F H (m+1))=0 by simp [unitVec,Size.unit_core]] at hc
    rw [show (Z (unitVec F H N)).x = T.leads L (unitVec F H (m+1)) from sub_eq_zero.mp (Work.G08.size_separates _ _ (by simpa [Frame.coeffSize] using hc))]
    change T.map (vowel F L _) = _
    rw [show vowel F L (unitVec F H (m+1)) = unitVec F H m from unit_vowel ..]; simp [unitVec,T.unit]
  · change IsLinearMap ℂ (fun v => (Z v).density 0 B R)
    simpa only [hp] using hP
  · intro v x
    change dance x ((Z v).density 0 B R)=(Z _).density 0 B R
    rw [hp,hp,hM]
  · refine ⟨fun v z=>?_⟩; change floatUp z 0 (M₀ v)= M₀ _
    rw [hMx,hMx]; simp only [Y,LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ← hq.moves]; exact concert z (V.index v) (fun i=> profile R.activities (Z₀ i).forced) -- Y,v infer
  · intro v
    let P' i:= Extra.Histories.stretch (Y v i) (O i)
    have he' i : Eligible (O i) A R y:= ⟨ht.coins,hF ..,_,hY ..⟩
    have hv' i: Eligible (Z₀ i) A R y:= ⟨ht.coins,(h₀ i).format,_,(h₀ i).bound⟩
    have ha := stanza (v:=y) (code _) P' (fun i=> stretch_rem (Y v i) (hY i.2 i.1)) Summable.of_finite (fun i=> (he' i).scaled _) (Eligible.mk ht.coins (hb' v).1 ⟨_,(hb' v).2⟩) Summable.of_finite
    change Eye (Z v) A R y= Lacing.load H N p A m L0 V _; rw [show Eye (Z v) A R y=∑' i,rooms _ F A _ _ (Eye (P' i) A R y) from ha.tsum_eq.symm,tsum_fintype]; unfold Lacing.load weaves; refine Finset.sum_congr rfl fun i _=>?_ ; dsimp only [P']; rw [(he' i).flare, show Eye (O i) A R y= _ from Eyelet.soar (n:=H.S.side m p) i.1 (u₀ i.1) (manySeat H p m) (h:=hv' i.2) (Z:=he' i)]; erw [heF]; rfl
  · intro v
    change Blown (Z v) 0 _ (c*orbitCost F*Dm (V.index v)); let t(j:Tally F):= c*Dm (J j.2)
    refine Blown.enlarge (Blown.pencil_joins (a:=t) (code _) ?_ Y v) (residual_bill F L c hc (V.index v)); intro j'
    have hVL:= Blown.spin (z:=j'.1) (hSnow j'.2) (u₀ j'.1) (h₀ _).format ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p))
    rw [show affine j'.1.1 (0:Site (H.S.side m p)) 0=0 by simp [affine], mul_div_cancel₀ _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (RoutesF.turnCost_near _)))] at hVL
    exact hVL
  refine ⟨X', Set.finite_iUnion fun m=> hk.image _,?_⟩
  intro v I R' x' -- let intros not function?
  let α(z:Tally F):= Motion.patch F z.1 (J z.2); let f z:= V.plays (V.index.symm (α z)); let e' z:= Extra.Histories.stretch (Y v z) (O z)

  have htP (z:Tally F):= Tale.travel (hhQ z) (Y v z)
 
  have hM₀(z:Tally F): Tale X' 0 0 ((↑L.val:ℂ)^d) (Y v z • (f z).exponentialEntry 0 B E) (Y v z • profile E.activities (f z).forced) (profile R.activities (e' z).forced) (Y v z * α z 0) (‖Y v z‖*(t+2*s)) (‖Y v z‖*(c*Dm (J z.2))) D:=by
     rw [show (e' z).forced= Y v z • (O z).forced from rfl, profile_scale]; exact htP z
  -- input series just linear maps by fixing.Complex.V actual
  apply Tale.upon hD hM₀
  · let g':= (IsLinearMap.mk' _ (expoLinear (T:=B) _ _ hq.book (fun i=> (hq.earns i).2))).comp V.index.symm.toLinearMap
    intro Ux
    
    have hyx: I.exponentialEntry 0 B R' Ux= (g' x') Ux:=by unfold I; change _=(V.plays (V.index.symm x')).exponentialEntry 0 B E Ux; rw [show V.index.symm x'=v from V.index.symm_apply_apply _]
    rw [hyx, ← fixing F g' x']; simp only [Finset.sum_apply]; exact hasSum_fintype _
  · let g'(v):= profile E.activities (V.plays v).forced
    let S:=(IsLinearMap.mk' g' (inkL V.plays V.charge hq.book (fun i=> (hq.earns i).2))).comp V.index.symm.toLinearMap
    intro i Ux
    have hyx: profile R'.activities I.forced i Ux= S x' i Ux:=by change _=g' (V.index.symm x') i Ux; rw [show V.index.symm x'=v from V.index.symm_apply_apply _]
    rw [hyx,← fixing F S x']; simp only [Finset.sum_apply]; exact hasSum_fintype _
  · intro j U
    exact profile_merge (code _) e' hy (fun j=> stretch_rem (Y v j) (hY j.2 j.1)) Summable.of_finite j U
  · have hxL : x'=∑ z:Tally F,Y v z • α z:= (fixing F LinearMap.id x').symm
    -- rw hxL only RHS
    rw [hxL]; simp only [Finset.sum_apply]; exact hasSum_fintype (fun z=> Y v z*α z 0)
  · refine ⟨fun i=> mul_nonneg (norm_nonneg _) (by positivity),Summable.of_finite,?_⟩; rw [tsum_fintype,← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (rip ..) (by positivity)
  refine ⟨fun j=> mul_nonneg (norm_nonneg _) (rem_nonneg (hY j.2 j.1)), Summable.of_finite,?_⟩; rw [tsum_fintype]; exact residual_bill F L c hc _
end YM.UVExtension.Lacing
