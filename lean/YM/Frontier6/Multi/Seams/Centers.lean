import YM.Frontier6.Multi.Toll.Paths
import YM.Frontier6.Multi.Seams.Shift
import YM.Frontier6.Pair.Witness
import YM.Frontier6.Exact.Palette

/-! A single ultrabranch below the accepted fuse suffices for every request,
   since we keep exact-limit rows independent of detector/exterior collection
   at a fixed request, with growth estimates through that cost valuation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Set Metric Lattice RG Wilson MergeProof Canopies Ribbons Accent Fareway Extra.Histories Bid
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage Push Marker Extraction Cells
open Canvas Platform Next.Extract Dash Spec
open scoped Topology BigOperators Classical
variable {G:Gauge}{O:Type}[Fintype O][DecidableEq O]
variable {C:Family G}{m j k b d:ℕ}{t:O→ℕ} (v:(i:O)→ C.label (t i)){H:Extraction.Order}
variable {S T:Table C.book}{L:ℕ→Table C.book}{R:Bin T}{Y:DiffPlan S}
variable (h:Base C H T L R S Y)(K:Spec.Final C H S) (hC:Realm C)(hG:G.Simple) (hW:Extraction.Wcmain C)
lemma Realm.twilight (hC:Realm C):PairProducer C:=by
   obtain ⟨W,r,D,h,hR,hZ,hP⟩:= hC.launches; exact ⟨hC.frame,hC.stops,hC.stores,W,r,D,h,hR,hZ.1⟩ -- clash name in Deep?
variable (ξ:Ultrafilter (ℕ×ℕ))(hξ:ξ.toFilter ≤ H.fuse)
-- local name later
def Centered (C: Family G)(ξ: Ultrafilter (ℕ×ℕ))(j:ℕ)(x: (i:ℕ×ℕ)→ Config G (C.side i.1 i.2)→ℂ)(w:ℝ):Prop := ∀ᶠ i in ξ.toFilter, ∃ h:j ≤ i.1, let T:=center C.S i.2 h 0; Interior (T.chamber 0) (x i) ∧ T.rootTest (C.beta i.1 i.2) (x i)≤ w
include h K hC hG hW hξ
lemma related (x:O→ Cover) (he:C.ref d≤ k) (hk:k ≤ m){y z z':ℝ}
    (hp:Stamped C m j k t x v H d y z)(hx:z<z'):
    ∃ Q:C.label d, ReferenceFit K Q m y ∧ Centered C ξ k (fun i=>leafGap C j d t x v i.1 i.2 Q) z':=by
    obtain ⟨w,hw⟩:=hp.probe; have hf : ∀ᶠ i in H.fuse,m ≤ i.1 ∧ Next.UVStress.quota C d m i.1 i.2 (w i) ≤ y:=hw.mono fun i hi=> ⟨hi.choose_spec.1,hi.choose_spec.2.1⟩
    have hA:= voyage_pitch C d d
    let A:=voyage C d m d*y; have ht: ∀ᶠ i in H.fuse, ‖w i‖≤ A:=hf.mono fun i hi=> (from_whole C h.family (p:=i.2) hi.1 (he.trans hk) _).trans (mul_le_mul_of_nonneg_left hi.2 (hA.pos _).le)
    obtain ⟨Q,hQ,hH⟩:=(isCompact_closedBall (0:C.label d) A).ultrafilter_le_nhds' (ξ.map w) (by rw [Ultrafilter.mem_map]; exact Eventually.filter_mono hξ (ht.mono fun i hi=>Metric.mem_closedBall.mpr (by simpa using hi)))
    have hT:Tendsto w ξ.toFilter (𝓝 Q):= hH
    refine ⟨Q,sublimit_grade h K (Realm.twilight hC) hG w Q hξ hT y (he.trans hk) hf,?_⟩
    unfold Centered; let D:=fun i=>w i-Q; have hD:Tendsto D ξ.toFilter (𝓝 0):= by simpa using! hT.sub_const Q
    filter_upwards [Eventually.filter_mono hξ hw, at_origin hξ hD hW he (z'-z) (sub_pos.mpr hx)] with i hV hd
    obtain ⟨N,p⟩:= i; let T:= center C.S p hV.choose 0; obtain ⟨he',hE,hq⟩:= hV.choose_spec;
    have hm (q':C.label d): leafGap C j d t x v N p q'= leafGap C j d t x v N p (w (N,p))+C.O N p (w (N,p)-q') 0:=by unfold leafGap; rw [show C.O N p (w _-q') 0=C.O N p (w (N,p)) 0-C.O N p q' 0 from (IsLinearMap.mk' _ (C.linearO ..)).map_sub _ _]; abel
    obtain ⟨hN,hP,hZ⟩:= hd; let f:= leafGap C j d t x v N p (w (N,p)); let g:= C.O N p (D (N,p)) 0
    refine ⟨hN, (?_),?_⟩
    · rw [hm]; exact (show Interior (T.chamber 0) f from hq.1).plus hP
    rw [hm]; exact ((seamless h.family N p).semi T f g hq.1 hP).trans ((add_le_add hq.2 hZ).trans_eq (add_sub_cancel ..))

omit h hC hG hW hξ
-- quota of each weight, not just full filtered fields.
lemma floors (w:ℕ)(hw:w≤d)(Q:C.label d)(y:ℝ)(hv:ReferenceFit K Q m y) :
   let F:= weight K w ∘L projectBelow K hw ∘L LinearMap.toContinuousLinearMap (S.project d)
   ‖F Q‖ ≤ ‖F‖*(voyage C d m (d-w)*y):=by
    intro F
    cases w with
    | zero=> exact (F.le_opNorm Q).trans (mul_le_mul_of_nonneg_left hv.whole (norm_nonneg F))
    | succ w=>
        obtain ⟨p,⟨x,hx⟩,he⟩:=hv.below w hw
        have ht' : F p=0:=by
           change weight K _ (projectBelow K hw (S.project d p))=0; rw [← hx];
           have hs:higher K hw (higher K w.le_succ x)=K.sector.derivatives.rise (show w ≤ d by omega) x:= higher_pass K w.le_succ hw x -- syntax hw.le
           rw [← hs,projects_fix]; exact weight_away K x w.lt_succ_self
        rw [← sub_zero (F Q),← ht',← map_sub]; exact (F.le_opNorm _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg F))
end YM.Frontier6.Road
