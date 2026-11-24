import YM.MS.ScaleForest.Budget
/-!
# Chart record, unit-scale costs and actual join integrands

Cost bounds on `disc R` for stars at log scale t, with z-holomorphy and
continuity at every contained point (these will include extensions in the
parameter disc when poles are canceled). Still *distinguish* these estimates
from the actual forest computation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {K : LineRule G} {X Y : Curtain G I} {p q : ℤ} {R a b c d S : ℝ}

abbrev Atlas (I:Type) (R:ℝ) := ↥(disc R : Set ℂ) × ℝ × I
def probe (F:Curtain G I) (R:ℝ) : Atlas I R → Mob G := fun x=> F x.1 x.2.1 x.2.2

structure Waves (R:ℝ) (p:ℤ) (F:Curtain G I) : Prop where
   sway: Sway (probe F R)
   hol (s : ℝ)(x:I): Hol (disc R) (fun z=> F z s x)
   token (z:ℂ): z∈disc R→ ∀ s x, Sturdy false (F z s x)
   funds (z:ℂ): z∈disc R→ ∀ s x, Goods p (F z s x)
theorem Waves.shrink (h : Waves R p X)(he : S≤R) : Waves S p X := by
   let M:=Metric.ball_subset_ball (α:=ℂ) (x:=0) he; let f:Atlas I S→Atlas I R:= fun q=> (⟨ q.1,M q.1.property⟩,q.2);
   exact ⟨ repaint h.sway f (by unfold f; fun_prop), fun i j=> (h.hol i j).mono M, fun z hZ=> h.token z (M hZ), fun z hZ=> h.funds z (M hZ)⟩
theorem Waves.forms (h:Waves R p X) (z:ℂ)(he:z∈disc R)(s:ℝ)(x:I): Form0 false (X z s x) := ⟨(h.hol s x).link he isOpen_ball,h.token z he s x⟩
theorem Waves.plus (h:Waves R p X)(H:Waves R p Y) : Waves R p (X+Y) :=
   ⟨ Sway_plus h.sway H.sway, fun s x=> (h.hol s x).add (H.hol s x), fun z hZ s x=> Sturdy_plus (h.token z hZ s x) (H.token z hZ s x),
   fun z hZ s x=> (good p G).add_mem (h.funds z hZ s x) (H.funds z hZ s x)⟩
theorem Waves.zero (p : ℤ)(R:ℝ) : Waves R p (0:Curtain G I) := ⟨fun _ _=> continuous_const,fun _ _=> Hol.zero,fun _ _ _ _=> Sturdy0,fun _ _ _ _=> (good ..).zero_mem ⟩
theorem Envelope.nearby (h : Envelope R a b X) : Vicinity (probe X R) := h.vicinity (J:=Atlas I R) (continuous_fst.comp continuous_snd) Prod.fst (Prod.snd ∘ Prod.snd)

-- THREE integrands. Input in co-moving momentum units.
def Ufor (K:LineRule G) (μ:ℝ) (X:Curtain G I) : Curtain G I := fun z t x => closeG K.half z (μ+t) (X z t x)
def Bfor (K:LineRule G) (X Y:Curtain G I) : Curtain G I:= fun z t x=> bridgeG K.half (X z t x) (Y z t x)
def Pfor (K:LineRule G) (μ:ℝ) (X Y:Curtain G I) (A:I→QP) : Curtain G I := fun z t x=> pinned K.half z (μ+t) (exp (-t) • A x) (X z t x) (Y z t x)

-- return to actual units at retained scale. These identities are before integration.
def backing (a:ℂ)(F:Curtain G I) : Curtain G I:= fun z s x=> plow a s (F z s x)

variable (K) (hR : Enough R)(hx : Waves R p X)(hy : Waves R q Y) {z:ℂ}(he:z∈disc R)(t μ:ℝ)(i:I)
   {A:I→QP}
include hx hR he

-- specialization at z=0 is not used here
omit hR in
theorem behind_u_for (a : ℂ) : backing a (Ufor K μ X) z t i = closeG (Alps.pulse 4 t K.half) z μ (backing a X z t i) := (closure_meter (K.ok.forms _) (hx.forms z he t i) t μ z a).symm
include hy
theorem behind_p_for : backing 0 (Pfor K μ X Y A) z t i=pinned (Alps.pulse 4 t K.half) z μ (A i) (backing 0 X z t i) (backing 0 Y z t i) := by
   simpa only [backing,Pfor,zero_add] using (pinned_meter (K.ok.forms _) K.ok.even K.ok.rev (hx.forms z he t i) (hy.forms z he t i) (hR.town he) t μ 0 0 (A i)).symm
omit hx hy he hR [TopologicalSpace I] in
theorem behind_b_for : backing 0 (Bfor K X Y) z t i=bridgeG (Alps.pulse 4 t K.half) (backing (-4) X z t i) (backing 0 Y z t i) := by unfold backing Bfor; rw [bridgeG_eq K.ok.rev,bridgeG_eq (a_rev t _ K.ok.rev), air_tree _ _ _ t K.ok.rev]; ring_nf
omit he
omit hR in
theorem WavesBfor : Waves R (p+q-2) (Bfor K X Y) := by
   have hB:=K.ok
   refine ⟨ swayBridge hx.sway hy.sway K.half, fun s x=> ?_, fun z hZ s x=> ?_,fun z hZ s x=> bridge_rank' (hx.funds z hZ s x) (hy.funds z hZ s x) K.half⟩
   · unfold Bfor; simp_rw [bridgeG_eq K.ok.rev]; exact (hx.hol s x).woods (hy.hol s x) (Hop.crate (K.ok.forms false).price)
   unfold Bfor; rw [bridgeG_eq K.ok.rev]; exact arboreal (hx.token z hZ s x) (hy.token z hZ s x) (K.ok.forms false).token K.ok.rev K.ok.even

variable [FirstCountableTopology I] (ht: Envelope R a b X) (hA : Continuous A)
include ht

omit hy in
theorem WavesUfor : Waves R (p-2) (Ufor K μ X) := by
   let Q:= K.ok.forms false; let Z: Atlas I R →ℂ:= fun i=> i.1
   refine ⟨?_,?_,?_,?_⟩
   · change Sway (fun i=> closeG K.half (Z i) (μ+i.2.1) (probe X R i))
     refine swayClose (I:=Atlas I R) (K:=K.half) (X:=probe X R) (V:=fun i=>μ+i.2.1) (Z:=Z) (N:=1) hx.sway Q ht.nearby ?_ ?_ ?_ ?_ ?_
     · intro i; exact hx.token _ i.1.property i.2.1 i.2.2
     · unfold Z; fun_prop
     · exact fun i=> hR.town i.1.property
     · exact fun i=> (hR.norm i.1.property).trans (by norm_num)
     · fun_prop
   · intro t x; exact holClose Q (hx.hol t x) hR.town isOpen_ball (fun i hi=> hx.token i hi t x) _
   · intro z hZ t x; simp only [Ufor,closeG_eq]; exact Sturdy_scale (torn (hR.town hZ) (hx.forms z hZ t x) Q).token (tenorK z (μ+t))
   intro z hZ t x; simp only [Ufor,closeG_eq]; exact (good (p-2) G).smul_mem (tenorK z (μ+t)) (goods_o (hx.forms z hZ t x) Q (hR.town hZ) (hx.funds z hZ t x))

include hA

theorem WavesPfor (hs:Envelope R c d Y) : Waves R (p+q-2) (Pfor K μ X Y A) := by
   have Q:= K.ok.forms false; let Z: Atlas I R →ℂ:= fun i=> i.1
   refine ⟨swayPinned (Z:=Z) (N:=1) hx.sway Q ht.nearby (fun i=> hx.token _ i.1.property _ _) (by unfold Z; fun_prop) (fun i=>hR.town i.1.property)
      (fun i=> (hR.norm i.1.property).trans (by norm_num)) (V:=fun i=>μ+i.2.1) (by fun_prop) (A:=fun i=>exp (-i.2.1) • A i.2.2) (by fun_prop)
      hy.sway hs.nearby (fun i=> hy.token _ i.1.property _ _) K.ok.rev K.ok.even, fun s x=> ?_,fun z hZ s x=> ?_,fun z hZ s x=>?_⟩
   · exact holPinned Q (hx.hol s x) (hy.hol s x) hR.town isOpen_ball (fun i hi=> hx.token i hi s x) (fun i hi=> hy.token i hi s x) K.ok.even K.ok.rev _ _
   · exact (placed_forms Q K.ok.even K.ok.rev (hx.forms _ hZ _ _) (hy.forms _ hZ _ _) (hR.town hZ) _ _).token
   exact placed_goods Q K.ok.even K.ok.rev (hx.forms _ hZ _ _) (hy.forms _ hZ _ _) (hR.town hZ) (hx.funds _ hZ _ _) (hy.funds _ hZ _ _) _ _
end YM.MS.ScaleForest
