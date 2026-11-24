import YM.MS.ScaleForest.Stertor
/-!
# Exponential horizon control of every placed piece

If we glue a vacancy, justify taking its answer to be zero: no legs
even if there's a unit term in that branch.
Prove the cost for driving all multi-pin components off the contact loci.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J : Type} [TopologicalSpace I] {X Y : Curtain G I} {R a b : ℝ} {p q : ℤ}

def Slipped (F:Curtain G I) (R:ℝ) : Prop:= probe F R=0
def Hover (F:Curtain G I) (p:ℤ) : Prop:= ∀ b:ℝ,0<b→∃ R:ℝ, Enough R ∧ Waves R p F∧ Envelope R (-b) (-b) F
def Paces (F:Curtain G I) (p:ℤ) : Prop:= ∀ b:ℝ,0<b→ b<1→∃ R:ℝ, Enough R ∧ Waves R p F∧∃a:ℝ, Envelope R a (vcost p b) F
def Crossing (F:Curtain G I)(p:ℤ) : Prop:= ∀ b:ℝ,0<b→b<1→∃R:ℝ,Enough R ∧ Waves R p F∧∀a:ℝ,Envelope R a b F
def MultiFuel (F:Curtain G I)(p:ℤ): Prop:= ∀ b:ℝ,0<b→ b<1→∃R:ℝ,Enough R∧ Waves R p F∧∀a:ℝ,Envelope R a (vcost p b) F

omit [TopologicalSpace I] in
theorem vacant (hx : Slipped X R) (a b : ℝ) : Envelope R a b X:= by
   intro J z s v; unfold OnTest
   have he (i:J) : X (z i) (s i) (v i)=0:= congr_fun hx (z i,s i,v i); simp_rw [he]; exact fall_zero (fun i=>(posLevy _ _ _).le)

-- helpers for the arity issue in the price calculation
section
variable {K : Rip G} {F H : Mob G} (h : Goods 0 F) (x:ℂ)
include h

theorem empty_close (hp : Form0 false F)(he: Knot false K)(hv:x∈Town)(y:ℝ) : closeG K x y F=0 := by
   have hz:= goods_o hp he hv h; funext m w; rw [closeG_eq]; simp only [Pi.smul_apply]; rw [ranks_off hz _ (by omega),smul_zero]; rfl

theorem emptyBridge : bridgeG K H F=0:= by
   funext m w; unfold bridgeG; rw [scatter_congr _ w _ 0 (fun s t _=> ?_)];
   · exact map_zero (allocate (field parity) w)
   exact Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> by rw [ ranks_off h _ (by simp; omega), mul_zero ]

private theorem emptyCut_l {m : ℕ} (q : SectorP m)(w : Legs (Shore G m)) : cutTree K F H q w=0 := by
   unfold cutTree; rw [scatter_congr _ w _ 0 (fun l r _=>?_)];
   · exact map_zero (allocate (field parity) w)
   simp only [Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> by unfold oneCross; rw [ranks_off h _ (by simp; omega)]; ring
private theorem emptyCut_r {m : ℕ} (q : SectorP m)(w : Legs (Shore G m)) : cutTree K H F q w=0 := by
   unfold cutTree; rw [scatter_congr _ w _ 0 (fun l r _=>?_)];
   · exact map_zero (allocate (field parity) w)
   simp only [Finset.sum_apply]; exact Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> by unfold oneCross; rw [ranks_off h _ (by simp; omega)]; ring
omit h in
private theorem swept_0 (K:Rip G) (s:ℂ)(y:ℝ)(A:QP)(F H:Mob G) (hv: ∀ m (w : Wire (Cfield G m) ℝ (SectorP m)), cutWing K (rephase A F) H w=0) :
    pinned K s y A F H=0 := by
   funext m w; unfold pinned; rw [hv];
   have he : carpet (Px m) (0:(SectorP m×ℝ)×ℝ→ℂ)=0:= by funext p; unfold carpet; simp
   have ho (p:ℕ) : pruning p (0 : Tree ℝ ℂ)=0:= by
      induction p with
      | zero=> rfl
      | succ n ih=> rw [Arc.spent,ih]; have hz: Arc.d (0:Tree ℝ ℂ)=0:= by funext p; simp [Arc.d]
                    unfold chop; simp_rw [hz]; funext p; simp
   simp [swoop, he, coreC, ho,fetching,fetchP]

theorem emptyPin_l (y : ℝ) (A:QP): pinned K x y A F H=0:= by
   have hp: Goods 0 (rephase A F):= fun m w he=> by rw [rephase_test,h m w he,mul_zero]
   apply swept_0; intro m w; funext p; unfold cutWing symmetricCut; rw [emptyCut_l hp,emptyCut_l hp]; simp

theorem emptyPin_r (y:ℝ)(A:QP): pinned K x y A H F=0:= by
   apply swept_0; intro m w; funext p; unfold cutWing symmetricCut; rw [emptyCut_r h,emptyCut_r h]; simp
end

theorem enough_le (hR : Enough R)(ha:0<a)(hp:a≤R) : Enough a := ⟨ha,hp.trans hR.2⟩
lemma vcost_le (hb:0<b) (p:ℤ): vcost p b ≤ b := by unfold vcost; split_ifs <;> first|exact hb.le|rfl

theorem paceFuel (h : MultiFuel X p) : Paces X p:= by intro b hb hp; obtain ⟨R,hR,hT,hX⟩:=h b hb hp; exact ⟨ R,hR,hT,0,hX _⟩

theorem Crossing.plus (hx:Crossing X p)(hy:Crossing Y p): Crossing (X+Y) p:= by
   intro b hb hp; obtain ⟨R,hR,hT,hX⟩:= hx b hb hp; obtain ⟨S,hS,hU,hY⟩:= hy b hb hp
   let V:=min R S; have h1:V≤R:= min_le_left ..; have h2:V≤S:= min_le_right ..;
   exact ⟨ V,hR.pair hS,(hT.shrink h1).plus (hU.shrink h2),fun a=> ((hX a).shrink h1).add ((hY a).shrink h2)⟩

variable [FirstCountableTopology I] (K : LineRule G) (μ:ℝ)

theorem fueledP {A : I→QP} (h:AdmittedGap A) (hx:Paces X p) (hy:Paces Y q) : Crossing (Pfor K μ X Y A) (p+q-2):= by
   intro b hb hp; obtain ⟨R,hR,hT,u,hX⟩:= hx b hb hp; obtain ⟨S,hS,hU,v,hY⟩:= hy b hb hp
   let W:= min (min R S) (b/2); have hW : W ≤ min R S:= min_le_left ..; have h1:=hW.trans (min_le_left ..); have h2:=hW.trans (min_le_right ..); let H:=enough_le (hR.pair hS) (show W>0 from lt_min (lt_min hR.1 hS.1) (half_pos hb)) hW; obtain ht:= hT.shrink h1; obtain hu:= hU.shrink h2; obtain hz:= hX.shrink h1; obtain hZ:= hY.shrink h2;
   refine ⟨ W,H,WavesPfor K H ht hu μ hz h.sails hZ,fun a=> ?_⟩;
   by_cases hρ : p=0
   · subst p; exact vacant (X:=Pfor K μ X Y A) (R:=W) (funext fun i=> emptyPin_l (ht.funds (i.1:ℂ) i.1.property _ _) i.1 _ _) a b
   by_cases hζ:q=0
   · subst q; exact vacant (X:=Pfor K μ X Y A) (R:=W) (funext fun i=> emptyPin_r (hu.funds _ i.1.property _ _) i.1 _ _) a b
   apply (wrapP K H hz hZ ht hu μ h a).relax le_rfl; rw [vcost,vcost,if_neg hρ,if_neg hζ]; linarith [show W ≤ b/2 from min_le_right ..]

omit [FirstCountableTopology I] in
theorem fueledB (hx:Hover X p)(hy:MultiFuel Y q): Crossing (Bfor K X Y) (p+q-2):= by
   intro b hb hp; let ε:=(1-b)/2; have he : ε>0:= by unfold ε; linarith
   obtain ⟨R,hR,hT,hX⟩:= hx ε he; obtain ⟨S,hS,hU,hY⟩:= hy (b+ε) (by linarith) (by unfold ε; linarith)
   refine ⟨ min R S,hR.pair hS,WavesBfor K (hT.shrink (min_le_left ..)) (hU.shrink (min_le_right ..)),fun a=> ?_⟩;
   by_cases hz:q=0
   · subst q; exact vacant (X:=Bfor K X Y) (R:=min R S) (funext fun i=> emptyBridge ((hU.shrink (min_le_right ..)).funds _ i.1.property _ _)) a b
   have ht:= wrapB K (hX.shrink (min_le_left R S)) ((hY (a+ε)).shrink (min_le_right ..))
   rwa [vcost,if_neg hz, show -ε+(a+ε)=a from by ring, show -ε+(b+ε)=b from by ring] at ht

theorem fueledU (hx:MultiFuel X p): Crossing (Ufor K μ X) (p-2) := by
   intro b hb hp; let ε:=(1-b)/2; have he:ε>0:= by unfold ε; linarith
   obtain ⟨R,hR,hT,hX⟩:= hx (b+ ε) (by linarith) (by unfold ε; linarith); let W:=min R (ε/2); have hW:W≤R:=min_le_left ..; let H:= enough_le hR (a:=W) (lt_min hR.1 (half_pos he)) hW; obtain ht:=hT.shrink hW; have hZ a:=(hX a).shrink hW;
   refine ⟨ W,H,WavesUfor K H ht μ (hZ 0),fun a=>?_⟩;
   by_cases hz:p=0
   · subst p; exact vacant (X:=Ufor K μ X) (R:=W) (funext fun i=> empty_close (ht.funds (i.1:ℂ) i.1.property _ _) _ (ht.forms _ i.1.property _ _) (K.ok.forms _) (H.town i.1.property) _) a b
   apply (wrapU K H (hZ (a+2*W)) ht μ).relax (by linarith); rw [vcost,if_neg hz]; linarith [show W≤ ε/2 from min_le_right ..]

theorem paidVertical (hx:Crossing X p): MultiFuel (vertical X) p:= by
   intro b hb hp; obtain ⟨R,hR,hT,hX⟩:= hx b hb hp; refine ⟨ R,hR, vertical_waves hT (hX 1) zero_lt_one (by linarith),fun a=> ?_⟩
   exact (reserveVert hT (hX (max a 1)) (lt_max_of_lt_right zero_lt_one) hb hp).relax (le_max_left ..) le_rfl
end YM.MS.ScaleForest
