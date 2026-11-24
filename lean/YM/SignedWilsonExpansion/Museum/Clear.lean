import YM.SignedWilsonExpansion.Homes.Universal
/-! # Ordered UV removal, fixed labels, same gauge families at moments
 Entire joint profile at the same RIGHT CLOSED address grid. Preserve all masks. Composite UV & period limits uniform compact `NoHit`, `conf` respectively (including ties). -/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Museum
open FullVolume Function Filter Set MeasureTheory Lattice Wilson RG Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open PhysicalNext.Repeat.Legato
open Extra.WeakScaling
open scoped Topology BigOperators ContDiff Classical
variable {ι I:Type*}{G:Gauge}{C:Family G}{n p:ℕ}{z:Filter ι}{b:ι→ℕ}

abbrev Ps (N:ℕ)(p:ℕ)(C:Family G)(n:ℕ):= (Fin n → Site (C.side N p))
local notation "X" => Points n

theorem continuouslyTested {K:Set X} (hm:IsCompact K)(H:Points n→ℂ) (F:ι→ Points n→ℂ) (k:ContinuousOn H K)
    (h:∀ U:Ultrafilter ι,(U:Filter _) ≤ z→ ∀ x∈K,∀ v:ι→X,Tendsto v (U:Filter _) (𝓝[K] x) → Tendsto (fun i=> F i (v i)) (U:Filter _) (𝓝 (H x))) : TendstoUniformlyOn F H z K:=by
   apply Metric.tendstoUniformlyOn_iff.mpr; intro ε he; by_contra! hv
   change ∃ᶠ i in z, ∃ x∈K, ε ≤ dist (H x) (F i x) at hv
   obtain ⟨U,u,a⟩:= (exists_ultrafilter_iff.mpr (frequently_iff_neBot.mp hv)).imp (fun _ hu=> le_inf_iff.mp hu)
   let P(i:ι)(x:Points n):= x∈ K∧ ε ≤ dist (H x) (F i x)
   let v (i:ι):Points n:= if h:∃ x,P i x then h.choose else 0
   have hV: ∀ᶠ i in (U:Filter _), P i (v i):= Eventually.mono (show ∀ᶠ i in (U:Filter _),∃ x,P i x from le_principal_iff.mp a) (fun i hi=> by rw [show v i=hi.choose from dif_pos hi]; exact hi.choose_spec)
   obtain ⟨x,hx,t⟩:= hm.ultrafilter_le_nhds (U.map v) (le_principal_iff.mpr (hV.mono fun i hi=> hi.1))
   have T: Tendsto v (U:Filter _) (𝓝[K] x):= tendsto_nhdsWithin_iff.mpr ⟨t,hV.mono fun i hi=>hi.1⟩
   obtain hh:= (((k x hx).tendsto.comp T).dist (h U u x hx v T)); rw [dist_self] at hh; obtain ⟨i,hv,p⟩:= ((hh.eventually_lt_const he).and hV).exists; exact hv.not_ge p.2

def genuine (C:Family G)(v:Fin n→ C.book.Token)(r:ℝ)(N p:ℕ)(x:Points n):=lifted C N p v (address (C.S.a N) (r • x))

lemma Round_limit (C:Family G) (e:Tendsto b z atTop){u:ι→Points n}{x:X} (h:Tendsto u z (𝓝 x)) (r:ℝ) : Tendsto (fun i=> Extraction.tag (C.S.a (b i)) (address (C.S.a (b i)) (r • u i))) z (𝓝 (r • x)):= by
   have hd : Tendsto (fun i=> (4*n:ℝ)* C.S.a (b i) ) z (𝓝 0) := by
      convert ((C.S.shrinks.comp e).const_mul (4*n:ℝ)) using 1
      · rfl
      rw [mul_zero]
   have hx:= h.const_smul r
   apply Metric.tendsto_nhds.mpr; intro ε he; filter_upwards [Metric.tendsto_nhds.mp hx (ε/2) (half_pos he),hd.eventually_lt_const (half_pos he)] with i hi hm
   exact lt_of_le_of_lt (dist_triangle _ (r • u i) _) ((add_lt_add (( approximate ( C.S.a_pos ( b i ) ) ( r • u i ) ).trans_lt hm) hi)|>.trans_eq (add_halves _))

abbrev Prism (S:Schedule)(K:Set (Points n))(p:ℕ)(r:ℝ): Prop:= MapsTo (fun x:X=>r • x) K (NoHit S p n)
variable (K:Set (Points n)) (r:ℝ) (φ:(I→ℂ)→ℂ) (k:IsCompact K)
include k in
lemma eligible (S:Schedule) (σ: K⊆ conf n)(hr:0<r): ∀ᶠ p in atTop, Prism S K p r:= (room S ( k.image ( continuous_const_smul r ) )).mono fun _ hi _ hv=> (no_wrap_hit S (hi (mem_image_of_mem _ hv))).2 (Work.A05.smul_conf hr (σ hv))
lemma contour (s:IsOpen K){x:X}{v:ι→Points n} (hx:x∈ K) (h:Tendsto v z (𝓝 x)): ∃ U:Set (Points n),IsCompact U∧ U ⊆ K∧ x∈U ∧ ∀ᶠ i in z,v i ∈ U:=by
   obtain ⟨U,hU,u,t⟩ := exists_compact_subset s hx
   exact ⟨U,hU,t,interior_subset u,h.eventually (mem_interior_iff_mem_nhds.mp u) ⟩

section interim
variable (hv:PositionsUV C Extraction.Sequence.full)(m:I→Fin n→C.book.Token)(w:Fin n→ C.book.Token) (hφ:Continuous φ)

abbrev amid (x:Points n):ℂ:= (hv p n w).choose x
lemma wawa : Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p w) (amid (p:=p) hv w):=(hv p n w).choose_spec.2.2 []|>.1
lemma interimA (e:Tendsto b z atTop){v:ι→Points n}{x:X}(t:r • x∈ NoHit C.S p n)(h:Tendsto v z (𝓝 x)) : Tendsto (fun i=> genuine C w r (b i) p (v i)) z (𝓝 ( amid (p:=p) hv w (r • x))):=by
   obtain ⟨U,g,v',w',t'⟩:= contour _ (nohitOpen C.S p n) t (Round_limit C e h r)
   obtain hh:= ((wawa hv w).1.mono v' _ w' |>.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ Round_limit C e h r,t'⟩ ))
   apply Metric.tendsto_nhds.mpr; intro ε ep
   filter_upwards [e.eventually (Homes.periodUsable (wawa (p:=p) hv w) U g v' (ε/2) (half_pos ep)), Metric.tendsto_nhds.mp hh (ε/2) (half_pos ep), t'] with i hi hM hu
   have he : dist (genuine C w r (b i) p (v i)) (amid (p:=p) hv w (Extraction.tag (C.S.a (b i)) (address (C.S.a (b i)) (r • v i)))) < ε/2 := by rw [dist_eq_norm]; exact hi _ hu
   exact lt_of_le_of_lt (dist_triangle _ (amid (p:=p) hv w _) _) ((add_lt_add he hM).trans_eq (add_halves _))
include k hφ in
lemma interimUniform (h:Prism C.S K p r): TendstoUniformlyOn (fun i x=> φ (fun j=> genuine C (m j) r i p x)) (fun x=> φ fun j=> amid (p:=p) hv (m j) (r • x)) atTop K:=by
   refine continuouslyTested k _ _ (hφ.comp_continuousOn (continuousOn_pi.mpr fun i=> (wawa hv ( m i )).1.comp ( continuous_const_smul r ).continuousOn h)) fun U u x hx v T=> (hφ.tendsto _).comp ( tendsto_pi_nhds.mpr (fun i=> interimA r hv (m i) u ?_ ?_ ))
   · exact h hx
   exact tendsto_nhds_of_tendsto_nhdsWithin T
end interim

section period
variable (R: Run G){f:Extraction.Order} (h:G.Simple) (hv:PositionsUV R.family Extraction.Sequence.full) {S:Table R.family.book} (hs:S.Smooth) (hX:(Homes.track f).PointLimits R.family S) (m:I→Fin n→ R.family.book.Token) (v:Fin n→ R.family.book.Token) (hφ:Continuous φ) {N':ι→ℕ×ℕ}
local notation "ℱ" => (Homes.track f)
include h hs hX
lemma clearP (t:Tendsto N' z (ℱ).fuse) {x:X}{v':ι→Points n}(u:r • x ∈ conf n)(q:Tendsto v' z (𝓝 x)) : Tendsto (fun i=> genuine R.family v r (N' i).1 (N' i).2 (v' i)) z (𝓝 (S.read ( r • x ) v)):=by
   have e:= Round_limit (b:=fun i=>(N' i).1) R.family ((cofin_fst ℱ).comp t) q r
   obtain ⟨U,g,v₁,v₂,t'⟩:= contour _ (conf_open n) u e; obtain hh:= ((S.smooth_read hs v).continuousOn.mono v₁ _ v₂|>.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨e,t'⟩))
   apply Metric.tendsto_nhds.mpr; intro ε ep; filter_upwards [t.eventually ( Homes.bright R h hs hX v U g v₁ (ε/2) (half_pos ep)), Metric.tendsto_nhds.mp hh (ε/2) (half_pos ep),t'] with i H hk ht
   exact lt_of_le_of_lt (dist_triangle _ (S.read _ v) _) ((add_lt_add (H _ ht) hk).trans_eq (add_halves _))
include k hφ
lemma orderUniform (hr:0 < r)(σ:K⊆ conf n): TendstoUniformlyOn (fun i:ℕ×ℕ=> fun x:Points n=> φ fun j=> genuine R.family (m j) r i.1 i.2 x) (fun x=> φ fun j=> S.read ( r • x ) (m j)) (ℱ).fuse K :=by
   refine continuouslyTested k _ _ (hφ.comp_continuousOn (continuousOn_pi.mpr fun i=> (S.smooth_read hs (m i)).continuousOn.comp ( continuous_const_smul r ).continuousOn fun x p=> Work.A05.smul_conf hr (σ p))) ?_; intro U u x hx v' T; refine (hφ.tendsto _).comp (tendsto_pi_nhds.mpr (fun i=> clearP r R h hs hX (m i) u ?_ ?_ ))
   · exact Work.A05.smul_conf hr (σ hx)
   exact tendsto_nhds_of_tendsto_nhdsWithin T

lemma periodUniform (hr:0 < r)(σ:K⊆ conf n) : TendstoUniformlyOn (fun i x=> φ fun j=> amid (p:=f.per i) hv (m j) (r • x)) (fun x=> φ fun j=> S.read ( r • x ) (m j)) atTop K:=by
   apply Metric.tendstoUniformlyOn_iff.mpr; intro ε ep
   have hM:= Metric.tendstoUniformlyOn_iff.mp (orderUniform K r φ k R h hs hX m hφ hr σ) (ε/2) (half_pos ep)
   change ∀ᶠ i in atTop, ∀ᶠ N in atTop,∀ x∈ K, dist (φ fun j=> S.read (r • x) (m j)) (φ fun j=> genuine R.family (m j) r N (f.per i) x)<ε/2 at hM
   filter_upwards [f.per.cofinal.eventually (eligible K r k R.family.S σ hr),hM] with i hi hS
   obtain ⟨u,H,hH⟩:=(hS.and (Metric.tendstoUniformlyOn_iff.mp (interimUniform (p:=f.per i) K r φ k hv m hφ hi) (ε/2) (half_pos ep))).exists
   exact fun x hx=> lt_of_le_of_lt (dist_triangle _ (φ fun j=>genuine R.family (m j) r u (f.per i) x) _) ((add_lt_add (H x hx) ((dist_comm _ _).trans_lt (hH x hx))).trans_eq (add_halves _))
end period
end YM.SignedWilsonExpansion.Museum
