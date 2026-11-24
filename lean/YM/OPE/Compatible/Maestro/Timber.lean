import YM.OPE.Compatible.Maestro.Collect
/-! Quote temperature polylog when geometry chosen. Uniform bounds even if PBig exponent differs amongst clocks on different leaves. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory Finset
open scoped Topology Classical
open YM.OPE.Allot Series
variable {G:Gauge}{C:Family G}{I V:Type}{φ:Filter I}{T r : I→ℝ}{q:I→ℕ}{b n:ℕ}
lemma priced_sash (h:Tendsto T φ atTop)(hq:Round φ T (fun i=>β C (q i))) : Round φ T (fun i=>sash C (q i)):=by
   let k:= MergeProof.winter G 0; exact (((((Round.const (a:=1024) (by norm_num) h).mul hq).mul (hq.power k h)).mul (hq.power k h)).inv)
section
variable [PartialOrder V][Fintype V][OrderBot V](D:Origin V){η : ℝ} {s:I→V→ℝ}{Q:Finset V}
variable (hG:G.Simple)(A:Allot C)(h: Glowing D Q φ T s η)
set_option quotPrecheck false
variable (b d M:ℕ)
local notation "t"=>fun i=>schedule C b η (s i)
local notation "at!"=>fun i=>aperture D C b d η (T i) (s i)
local notation "J"=>fun i=> fun u:V=>min (at! i u) (t i u)
local notation "sp"=>fun i=> C.S.a i
local notation "pay"=> Lights.valve C (places V) b
local notation "g"=> fun i => 81*(course C b M i+1)
include hG A h
lemma tick_valve (v:V)(hv:v∈Q): Round φ T (fun i=>pay (g (t i v)) (t i v)) :=by
    refine valve_price A hG (lives D hG A h b hv) h.ray (thermal D hG A h b hv|>.up) (places_pos V) (d:=b) (L:=81*(5*M+1)) ?_
    filter_upwards with i; unfold course; nlinarith only [Nat.zero_le M,Nat.zero_le (gapL C b (schedule C b η (s i) v))]
lemma tick_receive (v:V)(hv:v∈Q): Round φ T (fun i=> Run.Below C.path (sash C (t i v)/2) (J i v) (finishAt D (t i) v)):=by
    let s' i:=s i (par D v); let p i:=schedule C b η (s i); let m i:= finishAt D (t i) v; let y i:= J i v; let F i:= at! i v
    have hp:= h.crowned.roots (par_le D v) hv; have hh:= stands D hG A h b hp; have hu:= arrive D hG A h b d (v:=v) (mem_union_left _ hv)
    have hs:Round φ T (fun i=> C.S.a (F i)/ C.S.a (m i)):=by
       refine (hu.2.div hh).adjust ?_; filter_upwards [(h.fade _ hp).eventually self_mem_nhdsWithin] with i hi; change C.S.a (F i)/s' i / (C.S.a (m i)/s' i)=_; have ht:0 < s' i:=hi; field_simp
    let f i:= C.S.a (y i)/C.S.a (m i); have he(i):0<f i:=div_pos (C.S.a_pos _) (C.S.a_pos _)
    have hz:Round φ T f:=by
       refine ⟨Eventually.of_forall he,(Score.steady (1:ℝ) h.ray).pointwise ?_ (Eventually.of_forall fun _=> (he _).le), hs.down.pointwise ?_ (Eventually.of_forall fun _=> (inv_pos.mpr (he _)).le)⟩
       · filter_upwards [series_angle D hG A h b] with i hi; exact (div_le_one (C.S.a_pos _)).2 (C.S.strictAnti.antitone (le_min (finish_aperture D b d _ _) (hi.timing _ _ (par_le D v) hv)))
       filter_upwards with i; refine inv_anti₀ (div_pos (C.S.a_pos _) (C.S.a_pos _)) (div_le_div_of_nonneg_right (C.S.strictAnti.antitone (min_le_left ..)) (C.S.a_pos _).le)
    exact ((priced_sash h.ray (thermal D hG A h b hv)).div (Round.const zero_lt_two h.ray)).mul (hz.power 4 h.ray)
-- global cap min
lemma fund : ∃ z:I→ℝ, Round φ T z ∧ ∀ᶠ i in φ,CutOrder.Expenses C D Q (t i) (J i) (g) b (z i):=by
    suffices h':∀ S⊆Q,∃ z:I→ℝ,Round φ T z∧ z ≤ 1∧ ∀ v∈S,∀ i,z i≤ pay (g (t i v)) (t i v) ∧ z i ≤ Run.Below C.path (sash C (t i v)/2) (J i v) (finishAt D (t i) v) by
        obtain ⟨z,hx,he,hb⟩:= h' Q (by rfl); exact ⟨_,hx,hx.pos.mono (fun i hi=> ⟨hi,he _,fun v hv=> (hb _ hv i).1,fun v hv=> (hb _ hv i).2⟩)⟩
    intro S hS; induction S using Finset.induction_on with
    | empty => exact ⟨fun _=>1,Round.const one_pos h.ray,fun _=> le_rfl,fun _ he=> False.elim (notMem_empty _ he)⟩
    | insert x s0 hx IH=>
       have hu : x∈Q:= hS (mem_insert_self ..); obtain ⟨z,hz,he,ht⟩:= IH (subset_trans (subset_insert x s0) hS)
       let b' i:= Lights.valve C (places V) b (81*(course C b M (t i x)+1)) (t i x); let a i:=Run.Below C.path (sash C (t i x)/2) (J i x) (finishAt D (t i) x)
       refine ⟨fun i=>min (min (z i) (b' i)) (a i), ((hz.less (tick_valve D hG A h b M x hu) h.ray).less (tick_receive D hG A h b d x hu) h.ray), fun _=> (min_le_left ..).trans ((min_le_left ..).trans (he _)),fun v hv i=>?_⟩
       rcases eq_or_ne v x with h|h; · subst x; exact ⟨(min_le_left ..).trans (min_le_right ..), min_le_right ..⟩
       have hf : min (min (z i) (b' i)) (a i)≤ z i:= (min_le_left ..).trans (min_le_left ..); obtain ⟨hK,hg⟩:= ht v (mem_of_mem_insert_of_ne hv h) i; exact ⟨hf.trans hK,hf.trans hg⟩
end
end YM.OPE.Arboreal
