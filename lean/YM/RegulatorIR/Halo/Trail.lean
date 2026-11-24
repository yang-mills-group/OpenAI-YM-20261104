import YM.RegulatorIR.Halo.Shell

/-!
# Duplicated-torus discrepancy for translated probes
No appeal to cover invariant properties. Absolute only for requested powers,
fixed finite release length. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo.Aug
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Sight Uniform
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side} {I :Type}
variable {S: Heir n G}(H:Reel S) (w:W) (T:S.Accounts)
variable {r j e p k a m s:ℕ} {L:Meter W}
lemma support_cost {T:Packet I r}(A:I→Room)(x:Room)(l:ℝ)(h:0<l)(i:ℕ)(H: Prim.Bounded T): markQ ((Premium.rooted (Tariff.native l h i) x).uses A) T≠⊤:=by
 let F:= ((Premium.rooted (Tariff.native l h i) x).uses A)
 unfold markQ quota
 rw [tsum_eq_sum (s:=H.toFinset)]; swap
 · intro i hi; rw [Set.Finite.mem_toFinset] at hi; rw [Function.notMem_support.mp hi,enorm_zero,zero_mul]
 apply ENNReal.sum_ne_top.mpr;intro a ha; apply ENNReal.mul_ne_top (by finiteness); change F.width a≠⊤
 have hl(g:Fin r→ℝ≥0∞)(h:∀ i,g i<⊤): (⨆ i,g i)<⊤:= lt_of_le_of_lt (iSup_le (fun i=> Finset.le_sup (f:=g) (Finset.mem_univ i))) (Finset.sup_lt_iff (by simp)|>.mpr fun i _=>h i)
 unfold Premium.width Tariff.diameter; apply ne_of_lt
 refine max_lt_iff.mpr ⟨max_lt_iff.mpr ⟨hl _ (fun i=>hl _ (fun p=>?_)),by simp⟩,hl _ (fun i=>?_)⟩ <;> change Tariff.amount _ _ _<⊤ <;> unfold Tariff.amount <;> finiteness

variable (HH:H.Follows T)(Z:T.Report m) (B :S.Supplies T L p k)(C: Amenities S L p k) (h:Common H)
local notation "T'" => tele H T w
local notation "E" => eternal H w
local notation "Z'" => gazer H T Z w HH

lemma relay_cost (j:ℕ)(he:j ≤ M w) z e r :
 markQ ((lpost H w j he).rooted (centre S w) a z) ((Z').main (sheet w j he z) e r)=markQ (S.census.rooted (fun _=>0) a (⟨w,j,he⟩:Page M)) (Z.main ⟨w,j,he⟩ e r):=by
 let x:= shiftE (S:=S) w (sheet w j he z);let F:= Equiv.piCongrRight (fun _:Fin r=> x)
 let U:= Z.main (Page.mk w j he) e r
 unfold markQ quota; rw [← F.tsum_eq]; apply tsum_congr; intro i
 exact congr_arg₂ (·*·) (congr_arg (fun x:ℝ=>‖x‖ₑ) (echos x U i)) (root_shape H w j he z i _)

variable {V: W→Portrait G} (hV:∀ i,BasisT m s (V i) (Z.main (Page.opening M i)))
include H C B hV h
-- cover mark fixed length/no scale transfer (no Ward of F assumed)
lemma core_mark (j:ℕ)(he : j≤M w)(hq:k≥a) :∀ e,e≤p → ∀ r, Claim light ((lpost H w j he).rooted (centre S w) a) 1 fun z=>(Z').main (sheet w j he z) e r:=by
 induction j with
 | zero=>
    intro i _ r; unfold Claim; simp_rw [relay_cost]; refine Carry.regular (Poly.standard light ?_);exact support_cost _ _ _ _ _ ((hV w).canopy i r)
 | succ j ih=>
    let F:= known H w j he;let A:= (fun _:Side=>delay (S:=S) w j he); let hv(z:Side):0<A z:= (E).hl ((stepf w j he z).next)
    let G:= F.incoming A hv; let K:=F.insideRoom A hv;let X:= F.outgoing A hv;let Hp:= grove H w h
    let g (z:Side):= (stepf w j he z).prev
    let YV(z:Side):=(tele H T w).bulk (g z) -- rename
    let U(z:Side):=(Z').main (g z)
    intro i hi r
    have hm p' (hp:p' ≤ p) r: Claim light (G.rooted (centre S w) a) 1 (fun z=>U z p' r):=by
       have hr:= ih (by omega) p' hp r; let B:= lpost H w j (Nat.le_of_succ_le he)
       exact Post.few_cover hv (M:=B) (fun z=> (E).climb (stepf w j he z)) hr
    have hx : ∀ n:ℕ,Claim light (K.rooted (centre S w) a) 1 fun w=> F.primary YV U w n i r:=by
       intro n
       cases n with
       | zero=> unfold Batch.primary; simp_rw [markHeat_first]; exact F.onto_bill (hm i hi r)
       | succ n=>
          apply Batch.issue F YV U (K.descent (beams H w C _ _) hq) (fun a ha r=>K.writes (F.fine_work (conflict H w T B j he (ha.trans hi)) (added H w C j he (ha.trans hi))) hq) (fun i=> GridStep.joint_vac_shape _ ((tele H T w).cap_b (fun i=> essential Hp i) _) (essential Hp (stepf w j he i))) _ _ (by omega)
          exact fun p' r hg _=>hm p' (by unfold Earlier at hg;omega) r
    have hb:= Claim.sum (L:=light) (B:=K.rooted (centre S w) a) _ (Finset.range (m+3*i+1)) (fun n _=>hx n) |>.draft_budget (K.descent (spurs H w C _ _) hq)
    have hh := F.out_post hb
    change Claim light (X.rooted (centre S w) a) 1 _; convert hh using 1; ext1 z;exact Eq.symm (congr_fun (congr_fun ((Z').step_m (stepf w j he z)) i) r)

-- single-step triangle wrappers
-- choose minimum k=14 & supplies mono for application
omit C B hV h H in
lemma Amenities.enough (h : Amenities S L p k)(he:k≥a): Amenities S L p a:= ⟨S.ceilingRoom.descent h.line he,S.ceilingRoom.descent h.mean he, fun i hi _ => S.ceilingRoom.writes (h.budget i hi _) he⟩
omit T C B Z hV h H in
lemma T_enough (T:S.Accounts)(H:S.Supplies T L p k)(he:k≥a): S.Supplies T L p a:= ⟨fun i hi _ => S.census.writes (H.bulk_price i hi _) he,H.bulk_deck⟩

lemma march_bill (j:ℕ)(he : j≤M w)(hq:14≤k) :∀ e,e≤p→∀ r,Claim light ((lpost H w j he).anchored (centre S w) 0) debt fun z=>(Z').deviation (sheet _ j he z) e r:=by
 induction j with
 | zero=>
    intro i _ r; have hx(z:Side):(Z').deviation (sheet w 0 he z) i r=0:=by change Deck.scroll _ _ - Deck.scroll _ _=0; exact sub_self _
    simp_rw [hx]; exact Claim.zeroQ
 | succ j ih=>
    let F:= known H w j he;let A:= (fun _:Side=>delay (S:=S) w j he); let hv(z:Side):0<A z:= (E).hl ((stepf w j he z).next)
    let G':= F.incoming A hv; let K:=F.insideRoom A hv;let X:= F.outgoing A hv;let Hp:= grove H w h
    let g(z:Side):=(stepf w j he z).prev; let t(z:Side):=(tele H T w).bulk (g z);let u(z:Side):=(tele H T w).orb (g z);let v(z:Side):=(Z').main (g z);let y(z:Side):=(Z').point (g z)
    intro i hi r; let C':= C.enough (show k≥glaze 1 from hq); let B':= T_enough T B hq
    let B₀:=lpost H w j (Nat.le_of_succ_le he)
    have hm(z): B₀.length z≤A z:=(E).climb (stepf w j he z)
    have hx (a) (h:a≤p) b : Claim light (G'.anchored (centre S w) 0) debt fun z=>(Z').deviation (g z) a b:= Post.few_orb hv hm (ih _ a h b)
    let W' z:=F.kick (fun z=>(Z').deviation (g z) i r) z
    letI : ∀ z:Side,Fintype (Book G (big w n (g z))):= fun _=>inferInstance
    letI :∀ z:Side,Fintype (Book G (big w n ((stepf w j he z).next))):= fun _=>inferInstance
    have hy : Claim light (X.anchored (centre S w) 0) debt fun z=> (Z').deviation ((stepf w j he z).next) i r-W' z:=by
       have hU:= Batch.node F t u v y (e:=i) (r:=r) (u:=0) (b:=1) (q:=6) (l₀:=A) (l:=A) (hl₀:=hv) (hl:=hv) le_rfl (beams H w C' j he) (fete H w j he) (fun z=>hort Hp (stepf w j he z)) (fun z _ _ _=>natural_o Hp _ _ _) (fun z _ _ _=>helium Hp _ (knows H T w h HH) _ _ _) (fun z=> essential Hp _) (fun z=>(tele H T w).cap_b (fun i=> essential Hp i) (g z)) (fun z=>(tele H T w).cap_o (fun i=>essential Hp i) (g z)) (fun i ha _=> conflict H w T B' j he (ha.trans hi)) (fun i ha _=> added H w C' j he (ha.trans hi)) (fun i ha _ hr=> Post.fewer hv (M:=B₀) hm (horizons H T C' B' HH h w j (Nat.le_of_succ_le he) i (ha.trans hi) _ hr)) (fun i ha r _=> Post.few_cover hv hm (core_mark H w T HH Z B C h hV j (Nat.le_of_succ_le he) (by omega) i (ha.trans hi) r)) (fun _=> ENNReal.one_ne_top) (debtCost H w j he) (fun i r h _=> hx _ (by unfold Earlier at h; omega) _) (K.descent (spurs H w C j he) (Nat.zero_le k)) (fun z=> suitable Hp (stepf w j he z)) m
       convert hU using 1; ext1 z; unfold Accounts.Report.deviation;rw [← (Z').step_p,← (Z').step_m];rfl
    have hW: Claim light (X.anchored (centre S w) 0) debt W' := F.out_mark (Claim.draft_budget (F.orb_bill_mark (hx i hi r)) (K.wrap_beam (K.descent (spurs H w C _ _) (Nat.zero_le k)) (fun z=> suitable Hp (stepf w j he z))))
    change Claim light (X.anchored (centre S w) 0) debt _; convert Claim.add hy hW using 1;ext1 z; exact Eq.symm (sub_add_cancel ..)
end YM.RegulatorIR.Halo.Aug
