import YM.LocalLTE.Crafts.Wharf
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
-- Variance at PRE for all.Cut.
open RG.Shoot Averaging
variable (K: Set ℝ) (g:ℝ→Source G n) {x₀:ℝ}(hK:x₀∈K){f w:ℝ→ℝ} (hq: ∀ x∈K, Local X p (g x) (f x) (w x)) (hh:Compared X p g K)
local notation "𝒪" => 𝓝[K] x₀
include hn hG hR hd hq hh hK hv
variable (α:ℝ)(M:ℕ)(F:ℝ→ ℕ→ EKey n→ Pot G n) (hF:∀ j≤M,∀ x∈K,∀ v:ℝ, 0<v→∀ᶠ y in 𝓝[K] x, Stocked p (Price.tubeX R p X) (F x j-F y j) v)
set_option quotPrecheck false
local notation "T" y=> azures c p R X (g y) M (delta (X.read (g y))) α (F y)
local notation "Z" y=> silt c R X (g y) M (delta (X.read (g y))) α (F y)
local notation "X₀"=> bells p R X M
local notation "V"=> Price.tubeX R p X
include hF
variable {w₀ q:ℝ→ℝ}(hD:∀ x∈K, Ingredients (Price.bells p R X M) (azures c p R X (g x) M (delta (X.read (g x))) α (F x)) p (q x) (w₀ x))
include hD hF
open Samples Ovens
omit hF hD hv hR hq hh hG hn hd hK
lemma influx {X:ℕ→ RegularAddress n}{c:ℝ} {f :ℕ→ ℝ}(h: anchored p X f c): SumBudget (fun i=> p.mass (X i).support (f i)) ((Fintype.card (Site n):ℝ)*c):=by
    let g (i:Site n)(j:ℕ):= if (X j|>.site)=i then p.mass (X j).support (f j) else 0
    have hx:= Price.total univ g (fun _=> c) (fun i _=>h i)
    have he (i:ℕ): p.mass (X i).support (f i)= ∑ j,g j i:=by unfold g; rw [Finset.sum_eq_single (X i).site (fun k _ h=> if_neg h.symm) (by simp)]; exact (if_pos rfl).symm
    rw [show (fun i=>p.mass (X i).support (f i))=(fun i=>∑j,g j i) from funext he]; simpa using! hx -- Site n simp card
include hF hD hv hR hq hh hG hn hd hK
lemma alongE (s : ℕ→ℝ)(h : ∀ i, s i∈K)(hl:Tendsto s atTop (𝓝 x₀)): ∃ (r:ℕ→ℕ) (u:ℕ→ℝ),StrictMono r∧ Summable u∧ ∀ x∈sample x₀ (s ∘ r),∀ i:ℕ,p.supBounds ((Price.bells p R X M).reg i).site ((Price.bells p R X M).reg i).support (((T x)|>.regular) i) (u i):=by
   obtain ⟨x,hx,hM⟩:= Price.zinc X K g α M F hD x₀ hK
   choose m hm using fun i:ℕ=> eventually_atTop.1 ((within h hl).eventually (Price.torque hR hv hG hn hd X K g hK hq hh α M F hF ((1/2:ℝ)^i) (by positivity)))
   let r (i:ℕ) := i + (Finset.range (i+1)).sup m
   have hu i : m i≤r i := le_trans (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _))) (Nat.le_add_left _ _)
   have H : StrictMono r := fun i j hij => add_lt_add_of_lt_of_le hij (Finset.sup_mono (Finset.range_mono
       (Nat.add_le_add_right hij.le _)))
   let A:= Price.bells p R X M; let N:ℝ:= (Fintype.card (Site n):ℝ); let W:= fun x=> T x
   choose C hr hC using fun i=> hm i (r i) (hu i)
   obtain ⟨u,hU,hV⟩:= Samples.overhead p (fun j i=> (hr j i).2.1) (fun i=> (A.reg i|>.support)) (hasSum_geometric_two.mul_left N) (fun i=> Price.influx (hC i))
   have he i:0 ≤ u i:= (hr 0 i|>.2.1).trans (hU 0 i)
   have ht : Summable x := Summable.of_nonneg_of_le (fun i=>(hx i).2.1) (fun i=> p.loMass _ _ (hx i|>.2.1)) (Price.influx hM).2.1
   have hv : Summable u:= Summable.of_nonneg_of_le he (fun i=>p.loMass _ _ (he i)) hV.2.1
   refine ⟨r,x+u,H,ht.add hv,fun y hy i=>?_⟩
   rcases hy with (rfl|⟨j,rfl⟩)
   · exact VerifiedReset.sup_le (hx i|>.2) (le_add_of_nonneg_right (he i))
   let v:= s (r j); let t i:=(W v|>.regular i); let w i:= (W x₀|>.regular i)
   change p.supBounds (A.reg i|>.site) (A.reg i|>.support) (t i) _; rw [show t i=w i-(w i-t i) by abel]
   exact VerifiedReset.sup_sub (hx i|>.1) (hr j i|>.1) (hx i|>.2) (VerifiedReset.sup_le (hr j i|>.2) (hU j i))
-- sequence complete also soft elements. root inflation hB at finite fixed volume
local notation "J"=>numbering (Price.Fol n)
lemma cascade (s : ℕ→ℝ)(h : ∀ i, s i∈K)(hl:Tendsto s atTop (𝓝 x₀)): ∃ r:ℕ→ℕ,StrictMono r ∧ PreBound p (fun x=> T x) (Price.bells p R X M) (sample x₀ (s ∘ r)):=by
    obtain ⟨r, z, Hr,hZ,hx⟩:= Price.alongE hR hv hG hn hd X K g hK hq hh α M F hF hD s h hl
    let t:= s ∘ r; have hs':Tendsto t atTop (𝓝[K] x₀):= (within h hl).comp Hr.tendsto_atTop
    obtain ⟨b,e,k,hr,he,hk,hw',hQ⟩ := hh.series x₀ hK t hs'
    let B y := |Averaging.delta (X.read (g y))|
    obtain ⟨m,hm⟩ := eventually_atTop.mp ((hs'.comp hr).eventually (hh.drifting hG hq hK zero_lt_one) |>.and hQ)
    let L j := b (j+m)
    obtain ⟨v,hv',hM⟩ := strictMono_subseq_of_tendsto_atTop (u:=L) (hr.comp (tendsto_atTop_mono (show id ≤ (· + m) from fun j => Nat.le_add_right j m) tendsto_id))
    let S:= sample x₀ (s  ∘  r  ∘  L  ∘  v); have ht:S⊆ K:= Samples.sample_sub hK (fun i=> h (r _)); let c₀:=B x₀+1
    have hB':0 ≤ c₀:= add_nonneg (abs_nonneg _) zero_le_one; have ht' i: t (L (v i)) = (s ∘ r ∘ L ∘ v) i:= rfl
    have hy (x:ℝ) (hx:x ∈ S): B x ≤ c₀∧ Push.BetaTransport.Majorizes p e k (X.read (g x)):=by
       rcases hx with (rfl|⟨j,rfl⟩)
       · exact ⟨le_add_of_nonneg_right zero_le_one,hw'⟩
       rw [← ht']; refine ⟨?_, (hm (v j + m) (Nat.le_add_left ..)).2⟩
       let D x:= delta (X.read (g x)); let y:=t (L (v j)); have hP: |D x₀ - D y| ≤1:= (hm (v j+m) (Nat.le_add_left ..)).1; exact le_trans (by simpa using abs_sub (D x₀) (D x₀-D y)) (add_le_add le_rfl hP) -- namespace edit
    let w:= quoteL R (n:=n) p c |α| c₀ e; let f i:= Sum.elim (w  ∘  numbering (LKey n)) (Price.unitH p R |α| c₀) (J i); have hF:Summable f:= by
       refine (J).summable_iff.mpr (Summable.sum _ ((numbering _).summable_iff.mpr (quote_series (n:=n) hR hv |α| c₀ he).2) (tallyH hR hv |α| c₀)) -- n args
    refine ⟨r ∘  L ∘ v,Hr.comp hM, Payments.pre_finite (p:=k) (q:=f) (Set.insert_nonempty ..) hk hF (fun x hx' i U=>⟨(hy x hx').2.hard i|>.2 U, ?_⟩) ⟨z,hZ,fun x hx' i=> hx x (?_) i⟩⟩
    · let Δ:= delta (X.read (g x)); let x':= brew X R c p g α x; change ‖Sum.elim (x'.logarithm) (Price.remises Δ α p R) (J i) U‖≤ f i; unfold f
      have hB : |Δ|≤ c₀:= (hy x hx').1; have hA:= abs_of_nonneg (add_nonneg (abs_nonneg α) hB')
      have hw : |α+Δ| ≤ 1*(|α|+c₀) := by rw [one_mul]; exact (abs_add_le ..).trans (add_le_add_right hB _)
      cases hJ:J i; next i=>
        refine (Local.quote_soft (v:=g x) (R:=R) (c:=c) hG α Δ (hy x hx').2.smooth (hq x (ht hx')).smooth (numbering _ i) U).trans ?_; dsimp only [Function.comp_apply,Sum.elim_inl]
        cases he':numbering (LKey n) i; next=> exact le_rfl
        next j=> simpa only [w,quoteL,Sum.elim_inr,one_mul] using L_dominate (R:=R) (p:=p) (c:=c) (Sum.inr j) (le_refl (0:ℝ)) hw (show |Δ|≤1*|c₀| from by rw [abs_of_nonneg hB',one_mul]; exact hB) hA.symm
      next i=>
       refine (Price.tending Δ α p R hR i|>.2.2 U).trans ?_; dsimp only [Sum.elim_inr]; unfold unitH Hret; split
       · rw [hA]; have he:0≤ High.price R i.2 p:= High.price_nn ..; have ht:=p.threshold_pos; have hv:=turnFee_pos p; rw [one_mul] at hw; gcongr
       exact le_rfl
    rcases hx' with (rfl|⟨j,rfl⟩)
    · exact Set.mem_insert ..
    exact sample_map x₀ t (L (v j))
omit hK
open Rack Ovens.Pipes
lemma harbor {u v : ℝ→ℝ}(hp:ContinuousOn u K)(hV:ContinuousOn v K) : Curve p (fun x=>finish R c p (Price.bells p R X M) (T x) (u x) (v x)) K:=by
    refine ⟨hp,hV,fun _ _ _ _=> rfl,fun _ _ _ _=>rfl,?_⟩
    intro ε he x ht; let A:= Price.bells p R X M; let J':= A.encoding.some; let S y:= (T y); let D y:= fused (folio G n) p (widen A (S y))
    change ∀ᶠ y in 𝓝[K] x,deviation p (D x) (D y) ε
    by_contra h; obtain ⟨s,hs,h⟩:= exists_seq_forall_of_frequently ((not_eventually.mp h).and_eventually (show ∀ᶠ y in 𝓝[K] x,y∈K from self_mem_nhdsWithin))
    obtain ⟨r,hr,hR'⟩:= Price.cascade hR hv hG hn hd X K g ht hq hh α M F hF hD s (fun j=> (h j).2) (hs.mono_right nhdsWithin_le_nhds)
    let a:= s ∘ r; have hx:Tendsto a atTop (𝓝[sample x a] x):= Samples.within (sample_map x a) ((hs.mono_right nhdsWithin_le_nhds).comp hr.tendsto_atTop)
    have hb: sample x a ⊆K:= sample_sub ht (fun i=> (h (r i)).2); have hP:= Price.aroma hR hv hG hn hd X K g hq hh α M F hF hD
    obtain ⟨i,hi⟩:= (hx.eventually ((hP.tighter hb).measured hR' J' (Set.mem_insert ..) ε he)).exists
    exact (h (r i)).1 (((hD _ ht).address R c (u x) (v x) J').compares ((hD (a i) (h (r i)|>.2)).address R c (u (a i)) (v (a i)) J') hi)
end YM.AnalyticBridge.VerifiedReset.Collection.Price
