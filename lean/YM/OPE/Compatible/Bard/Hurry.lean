import YM.OPE.Compatible.Bard.Foyer
/-!
# One report propagated in the second, centered tiling.
Finish pays at fixed aperture. Doesn't use the path thereafter on that tiling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank Edition
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G} (A:Allot C)
    {d b k N p J m:ℕ}{w:ℝ}{Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}
set_option quotPrecheck false
local notation "F"=> C.labels.level d
local notation "T"=> C.localSection d
local notation "P!"=> C.path
local notation "R"=> C.path.rep N p
local notation "B"=> R k
local notation "α"=> alto C.path k d
local notation "V!"=> Site (C.side J p)
local notation "S"=>stair (near C.path.levels) ((lantern C.path w d k) m) m
local notation "E"=> (Mix.camp C p J)
include A
-- use actual φ schedule, no rejection on T closure
lemma mocks {i:ℕ} (h:C.ref d ≤ m)(hh:m ≤ i)(hG:G.Simple)(hw:0<w): stair (near C.path.levels) ((lantern C.path w d k) m) m i ≤ (lantern C.path w d k) i:=by
   let r:=lantern C.path w d k; have hm:0<r m:=lan_pos C.path hw; have hi:0<C.S.a i/C.S.a m:=by apply div_pos <;> apply C.S.a_pos
   have hg:C.S.a i/C.S.a m ≤1:= (div_le_one (C.S.a_pos _)).mpr (C.S.strictAnti.antitone hh); let u:=fly C.path.levels d; have ht:0<u m:= A.buy.system.grows d m h; have hx:u i≤u m:=fly_le hG d m i hh
   refine (seeing (b:=r m) C d A.buy.system hm i m h hh).trans ((mul_le_of_le_one_right (by positivity) ((div_le_one ht).2 hx)).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hi.le hg d.le_succ) hm.le).trans_eq ?_))
   change w*(C.path.S.a m/C.path.S.a k)^d*(C.S.a i / C.S.a m)^d=w*(C.path.S.a i/C.path.S.a k)^d; rw [mul_assoc,← mul_pow]; have hv:= C.path.S.a_pos m; change w*(C.path.S.a m/_ * (C.path.S.a i / C.path.S.a m))^d=w*_^_; field_simp
variable (f:Config G (C.side N p)→ℂ)
lemma blot {c:ℕ→ℝ}(hP:C.Makes)(hG:G.Simple)(hK:Stock.Tabs.opens C.path.levels 1 J m)(hx:m<k)(he:k ≤ N)(hN:C.ref d ≤ m)(hw:0 < w)
    (hv:Club C.path C.params (C.localSection d) (fly C.path.levels d) (waybill C.path.levels) (C.ref d) k N p (lantern C.path w d k) A.D Z c he)
    (hf:Continuous f)(hh:Served (R k) (fun i:V!=> radiant α (hands C p J i) (Mix.camp C p J k i) ((Z k).exponentialEntry 0 (C.localSection d) (C.path.rep N p k))) (fun i:V!=> sunny (B) (Z k).forced (hands C p J i) (Mix.camp C p J k i) α) (gust C.path N p N (birth (Bud V!) (R N) (fun i=> (Cells.center C.S p (hK.1.trans (hx.le.trans he)) 0).copy i f)) k he) (E k) (fun _=>w) ((bins C k).supportExponent-3) 1): (Cells.center C.S p (hK.1.trans (hx.le.trans he)) 0).rootTest (C.beta N p) f ≤ stakes C J m/lantern C.path w d k m:=by
   let u:=lantern C.path w d k; let s:=stair (near C.path.levels) (u m) m; have hp(i)(ht:m≤ i): s i ≤ u i:= mocks A hN ht hG hw
   have hB:Club C.path C.params (C.localSection d) (fly C.path.levels d) (waybill C.path.levels) m k N p s A.D Z c he :=by
       refine ⟨fun i hi hk=> hv.ticks i (hN.trans hi) hk,fun i hi hk=> ?_,fun i hi=> hv.votes i (hN.trans hi)⟩
       exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hp i hi) (norm_nonneg _)) (add_nonneg (rem_nonneg (hv.ticks i (hN.trans hi) hk|>.2)) (Work.G08.size_nonneg ..))).trans (hv.rates i (hN.trans hi) hk)
   let Y i:= (Cells.center C.S p (hK.1.trans (hx.le.trans he)) 0).copy i f; let b:= Bud V!
   have hu:0<u m:=lan_pos C.path hw; let q:= birth b (R N) Y; let Y0:=gust C.path N p N q
   have hY(i:V!):Continuous (Y i):= cappedC C J p N _ (fun _=> f) (i,false) hf
   have hI:Integrable q (prior G _):= (hatCont C N p _ hY (show Continuous (R N|>.eval) by rw [(hP.wilson.starts ..).2]; exact bare_cont _) _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   let t:= hands C p J; let J':= hK.1.trans hx.le; let q':= march (fun _ : V!=>u m) (near C.path.levels) m;
   have hw'(i:V!): ∀ j:ℕ,q' j i=s j:=by
       intro i'; induction i' with
       | zero=>rfl
       | succ j ih=> by_cases hf:m≤ j; dsimp only [s,q',stair]; simp only [march,if_pos hf]; exact congr_arg _ ih -- maybe simp changes
                     simp [s,q',stair,hf,march]
   let φ:=near C.path.levels
   have hv':Brine C.path m (renal C.path.levels) φ:= ⟨fun i _=> A.buy.system.costs.stay.water _ (Nat.zero_le i),fun i _=> A.buy.system.costs.stay.mint _ (Nat.zero_le i),fun i _=> A.buy.system.costs.stay.split _ (Nat.zero_le i),fun i _=> A.buy.system.costs.stay.support _ (Nat.zero_le i)⟩
   have hk : ∀ i,0 < q' k i:= fun i=> march_pos _ _ _ _ _ (fun _=>hu) hv' k hx.le i
   have hq(i):q' k i≤ w:= (hw' i k).le.trans ((hp k hx.le).trans_eq (lan_home ..))
   have hi' := hh.prune (d:=1) (fun _=>hw) hk (slighter (fun _=>hw) hk (w:=1) (fun i=> (hq i).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (show ((bins C k).supportExponent-3)+0 ≤ ((bins C k).supportExponent-3) by linarith only) (le_of_eq (mul_one _))
   have hM : Migrating C.path m p k E:= uphill C J m p k hK.1
   have h₀:= Work.I03.answer G C 1 le_rfl A.buy.tabs J m hK k hx.le p J'
   have hA: Edition.Spaced (C.path.levels.budget m|>.B) (E m):=fun i j hij=>by have ht:= h₀.2.2 m le_rfl hx.le i j hij; rw [mul_one] at ht; exact_mod_cast ht
   obtain ⟨hV',hz'⟩:= peek (M:=Y0 k he) C N k m p d hP (u m) A.buy.system E t (fun _ : V! => fun _ : Unit=> (1:ℂ)) (fun _=>Z) he hN hx (gust_live _ _ _ _ _ hI _) hM (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (C.path.levels.budget m|>.B_pos) hA) i).trans (A.buy.system.back m)) (show Drake b _ (E m) from ⟨fun _ _ i _ j _=> hA i j⟩) (x:=fun _=>u m) (g:=fun _=>c) (fun _=>hB) (by simp only [Finset.sum_const,Fintype.card_unit,one_smul,Finset.card_univ]; exact hi') hu (fun _=>hu) (by intro i; simp [ne_of_gt hu])
   unfold Y0 at hV'; rw [drifting] at hV'
   let A':= Fintype.card V!
   let t':=(C.S.a J/C.S.a m)^4*Vac.treasury (P!).levels m+ (5:ℝ); let r:= Stock.final V!; let W:=moment (C.beta N p) (fun x=>∏ i∈r.val,Y i x)
   have hq: Integrable (fun x=> ∏ i∈r.val,Y i x) (law G (C.side N p) (C.beta N p)):= (continuous_finsetProd _ fun i _=> hY i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   have h' := vista P! b N p m Y (X:=Y0) (fun i _ hx=>gust_step ..) (gust_base ..) (by rw [show Y0 N _=q from gust_base ..]; exact hI) hP.wilson (hx.le.trans he) r hq hV' hz' (fun _=> hu) (C.path.levels.budget _|>.exponent_pos.le)
   unfold Cells.Tiling.rootTest; refine Stock.spacer ‖W‖ t' (u m) A' (norm_nonneg _) hu Fintype.card_pos ?_
   rw [show Poly.toll (fun _ : V!=>u m) r=(u m)^A' from by simp [Poly.toll,A',r,Stock.final], show (Fintype.card (Site (C.side m p)):ℝ)*Vac.treasury (C.path.levels) m+(A':ℝ)*(2+1+2*1)=A'*t' from by rw [Stock.tallies C.S J m p]; unfold t' A'; ring] at h'; exact h'
end YM.OPE.Allot
