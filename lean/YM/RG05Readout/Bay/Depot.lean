import YM.RG05Readout.Halls.Siren
import YM.RG05Readout.Flatten.Village
/-!
# Depot at measuring fields. Price one-genuine-array Crop.
For any sufficiently deep author and all N further, even varying p.Seek
any positions through those all preimages, arbitrary normalized test body
and all particle wards. Interlocking downstream leases must use the same
threshold pencils and orientations.This part bounds actual U trial as a
 (normalized) tensor spectator. No perturbative valuation assumed. Costs
at fixed b geometry, used for physical filtration and Gram, not a priori
in Powers.Limit.stages. Adapted from Shadows terminal and Halls SIREN.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Bay
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {j b k l:ℕ}{e Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "L"=> C.path.levels
local notation "χ"=> C.path.levels.clock.J
local notation "λ"=> C.S.toDepth
local notation "Α"=> C.S.a
local notation "Z"=> C.path.levels.budget
local notation "R0"=> C.path.rep N p
variable {V:Address.Sight C d p}{U:Address.Emblems C d}(hw:Awake D B b d)(ht:Spine D B h b p d N V U)
include hw h
lemma wrapped_known {P:Tape G (C.side b p)} {v w:Palette C d}(hc:b < N)(hp:Printed C d (C.path.rep N p b) 0 (kappa C.path b) P v w e): size v ≤ size w + e:=by
    refine (size_compare v w).trans (add_le_add_right ?_ _)
    obtain ⟨s,K,c,β,T,Q,H,hT,hX,hu,-⟩:= (hw.toll p b N le_rfl hc).author
    let S:=H.cursor.sense d le_rfl
    have ht:= wraps_paid d C hp S.order S.power; rw [(h.wilson.represents N p b hc.le).vac] at ht
    obtain ⟨hz,-⟩:= max_le_iff.mp hu
    rw [size_turn]; exact ht.trans (mul_le_of_le_one_left hp.nonneg (hz.trans (thin_one ..)))

local notation "ν"=> Many.envelope C (b+1) (d+1) k Q b
local notation "E"=> total C Q (d+1) (b+1) b
noncomputable def sequin (C:Family G)(b d:ℕ)(B:ℕ→ℕ→ℝ)(Q:ℝ):ℝ:= let t:=Many.total C Q (d+1) (b+1) b; harvestCost C d b*(t+2*(B d b*t))
local notation "u"=> sequin C b d B Q
variable {w:Worth}{r:ℕ→ℕ}(Yc:OPE.Package C w r D) (Ys:Storage C D)
-- caps
variable {I:Type}[DecidableEq I][Fintype I] (y:I→Site (C.side b p)) (F:I→Motion) (i':Body) (he:Cap (d+2) i' 1) (M:Palette C d)
local notation "A" => Mine.tree y F
local notation "T"=>ManyStem C y
local notation "C!"=> Mine.ward y F (Stock.census I)
local notation "X"=> Many.point U M (b+1)
local notation "J'"=> fun i:I => Launch (m:=b+1) (fun _ : I=>d) (fun _=>U) (fun _=> M) i
local notation "g"=> headings y F (fun _=>i')
local notation "Z!"=> swell (le_refl N) (Mine.tree y F) (fun _ => d) (fun _=> precinct C p N d (X N)) g
include ht Yc Ys he
set_option maxHeartbeats 620000 in
lemma inSequence (hp:b<N)(hM:size M ≤ Q)(hQ:0<Q)(hX:Warm C b (d+1) k)
    (hx:GapAll ((Z b).B^2+1+0) (C.side b p) y) (hy:1 ≤ C.path.levels.clock.J b) (s:(C! b).Mode):
    0< Many.envelope C (b+1) (d+1) k Q b ∧ ‖C.omega N p (fun V₁=>∏ i∈s.val, Z! b i V₁)‖*(ν)^s.val.card≤ Real.exp ((Fintype.card (Site (C.side b p)):ℝ)* Vac.treasury C.path.levels b+ Fintype.card (T b)*(ν*u+ν*u+2*1)):=by
    have hC':Warm C b (d+1) k:=hX; have hV:0<ν:=mul_pos (rust_paid _).1 (grantw (totalpos hQ _)); refine ⟨hV,?_⟩
    let a:= (A); let f:=g; let q:= Z!; let W:= (C!); let t:=ν; let v := plants (m:=b+1) (fun _ : I=>d) (fun _=> V) (fun _=>U) (fun _=> M); let Vt:= imprint h (A) f v b hp.le; let P:= birth (W N) (R0 N) (q N)
    have hf : P= birth (W N) (R0 N) (fun i=> stepUp ((A).motion ((A).labelY N i)) ((A).supportX N i) (entrance C d N p (Many.point U M (b+1) N) 0 (g N i))):=by
      unfold P; congr 1; unfold q; funext i; exact staples ..
    have hi:Integrable P (prior G _):= by rw [hf]; exact seen_top (H:=W) (v:=fun _ : I=> X) (A) (fun _=>d) g h
    obtain ⟨G',hE,hL⟩:= wind y F (fun _=>d) hp.le P
    obtain ⟨hh,hF⟩:= Many.headlines y F (fun _=> i') (N:=N)
    have hG:∀ i:T b,Cap (d+2) (f b i) 1:=fun i=> by unfold f; rw [hh]; exact he
    have hK: MenuBoard (R:=W b) (R0 b) Vt (G' b) ((A).supportX b) (fun _=>t) ((Z b).supportExponent) 1:=by
       have hC:Clearance y F (fun _:I=>d) (g) (Stock.census _) (b+1):= by
          intro s _ i hi j hj h; have hL:Lit (Stock.census I) ((A).labelY (b+1)) s.val:= (Finset.mem_filter.mp s.property).2
          exact le_trans (b:= (Z (b+1)).B^2+1+0) (by omega) (grantG y Yc.tabs hx b.le_succ i j (fun h'=>h (hL.2 hi hj h')))
       have ht':= docks y F (fun _:I=>d) g h Yc Ys (fun _=>V) (fun _=>U) (fun _=>M) (fun _=>ht) b.le_succ hp (fun i=> (gap_one y hx (by omega) i).trans hy) hC hF hG (fun _=>hM) hQ hX (fun _=>le_refl d) (hL.trans hf) hE b le_rfl b.le_succ
       dsimp only at ht'; rw [if_neg (by omega)] at ht'; exact ht'
    have hxL: size (X b) ≤ E:= head_cost ht b.le_succ hp (le_refl (d+1)) hM le_rfl hp.le
    have hQQ: 1 ≤ B d b:=(ht.legal b le_rfl hp.le).pos
    have he_L: 0 ≤ harvestCost C d b:= mul_nonneg (add_nonneg zero_le_one (feepos d).le) (add_nonneg (by norm_num) (zero_le_one.trans (Stage.columns_ge _)))
    obtain ⟨c,hc⟩:= (ht.legal b le_rfl hp.le).capacity0 (X b); have hp': size c+ B d b*size (X b) ≤ E+2*(B d b*E):=by
        linarith only [mul_le_mul_of_nonneg_left hxL (zero_le_one.trans hQQ),hxL,wrapped_known h hw hp hc]
    have hf'(i:T b)(U'): t*coinCost (R0 b) (Vt i) U' ≤ ν*u:=by
       rw [coin_after ((A).motion ((A).labelY b i)) ((A).supportX b i) _ (show Signpost (R0 b) _ _ ((V b (X b)) (f b i)) (Vt i) from View.spin_at ..)]; exact mul_le_mul_of_nonneg_left ((Shadow.priced h hw hp.le hc (hG i) _).trans (mul_le_mul_of_nonneg_left hp' he_L)) hV.le
    let t':Config G (C.side N p)→ℂ:= fun V₁=> ∏ i∈s.val,Z! b i V₁
    have hZ: Vault (fun _ : T b=> t) (fun i=>(Vt i).snd.1) (fun i=>profile (R0 b).activities ((Vt i).snd.2)) (ν*u) (ν*u):=by
        refine ⟨fun i U'=>(mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=> norm_nonneg _))) hV.le).trans (hf' i U'),fun i U'=>?_⟩
        rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg _)) hV.le).trans (hf' i U')
    -- stock certificate
    have hE := spiker C N b p h s (C.omega N p t') hp.le (fun _=>hV) hK.grants hZ hK.cleared ?prep
    swap
    · obtain ⟨hy',hy''⟩:= reimburses (A) (fun _=>d) (le_refl N) q (le_refl b) hE (fun i hi' h' => pillar _ _ _ _ hi' h' (hF i hi' h')) (by rw [gust_base]; exact hL) hi le_rfl hp.le
      have hpP (i:T b):Continuous (q b i):= clinic_cut ..; rw [hy'']; have H:= Aligned.paid_by_partition h (q b) hy' hp.le s (continuous_integrable _ (continuous_finsetProd _ fun i _=>hpP i)); rw [History.partition_eq C.path h.wilson N p b hp.le] at H; exact H
    unfold Poly.toll at hE; rw [Finset.prod_const] at hE; exact hE
end YM.RG05Readout.Bay
