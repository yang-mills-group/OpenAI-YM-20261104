import YM.RegulatorIR.Profiles.Trek

/-!
# Produce internal RegulatorRemovalBudget through point centers

Receives independent single-F normalization cost via `roster`; all other
analytic premises stay cover/fold-band powers. No cluster estimate assumed.
Clearance to fold required for comparing (not for aperture authentication).
Rates contain all measuring growth explicitly. Stationary angle center fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Collapsed
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I:Type}{q u b p a i e k:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{J D:Choice M}
variable {S:Heir n G}{R: Reel S}{Γ: Flap M → Layer (Foot G) (Foot G)}{V: Flap M → Bride G}
  {c: Flap M→ℝ≥0∞} {T:S.Accounts} {m s H:I→ℕ}
variable (K:Composite I)(P:I→W→Portrait G)(Z:∀ i,T.Report (m i))
variable {x: W→Room}{σ:I→ℝ} {D':I→W→Set Room} {d: W→ℝ}

abbrev plusU (b u:ℕ):=u+b+b
def tileC (u a:ℕ):ℕ:= u+u+a
def transitK (b u a:ℕ):= max (tileC (plusU b u) a) (quantum b u)
abbrev dawn (D:Choice M)(S:Heir n G):= D.before.expanse S
abbrev individual (Z:∀ i,T.Report (m i)) (D:Choice M)(i:I)(p:Page D.before.spans) := (Z i).main (D.before.page p)
abbrev tasks (D:Choice M)(S:Heir n G) (L:Meter W) (p:ℕ)(Q: (v:Page D.before.spans)→Orders (Foot G)) (u a:ℕ)(U: W→Set Room)(σ:ℝ)(h:ℕ):Prop:= Folds p (coverL D.before.spans L) (estate (dawn D S).hl (Stations (dawn D S)) (U ∘ Page.bindW) (tileC u a)) (topGrowth (dawn D S) σ h) Q
-- use height index m independent from a growth.
structure Typical (x:W→Room)(D':I→W→Set Room)(d:W→ℝ)(K:Composite I)(L:Meter W) : Prop where
 present : ∀ i,K.In i→∀ w,(D' i w).Nonempty
 close : ∀ i,K.In i→∀ w,IsClosed (D' i w)
 apart : ∀ w,K.Distinct (fun i=>D' i w) (d w) -- field notation? first Composite implicit?
 clear : ∀ w,0<d w
 space : ∃ r:W→ℝ,Poly L (fun w=>ENNReal.ofReal (r w)) ∧ ∀ w,0≤r w ∧ ∀ y∈area K D' w,dist y (x w) ≤ r w
 rate : Poly L fun w=> ENNReal.ofReal ((d w)⁻¹)
structure Rosters (P:I→W→Portrait G)(Z:∀ i,T.Report (m i))(D:Choice M)(p u a:ℕ)(σ:I→ℝ)(H s:I→ℕ)(D':I→ W→Set Room)(L:Meter W)(K:Composite I): Prop where
 ink : ∀ i,K.In i→∀ w,Halo.BasisT (m i) (s i) (P i w) ((Z i).main (Page.opening M w))
 wide : ∀ i,K.In i→ tasks D S L p (individual Z D i) u a (D' i) (σ i) (H i)
 nonneg : 0≤K.loss σ
section Caps
variable (A: SchemeBeam R T Γ V L c p k)(B:Rosters P Z D p (plusU b u) a σ H s D' L K)(C:Typical x D' d K L)
  {γ:ℝ} (N: Lantern S D L c γ)(hb:0<b)(hk:transitK b u a≤k)
omit A B C N in
lemma fifteen (hb:0<b)(hk:transitK b u a ≤ k):14≤ k:= by unfold transitK quantum at hk;omega
lemma begins (u a:ℕ) : quantum b u ≤ transitK b u a:= le_max_right ..
include A B C N hb hk
lemma cluster : ClusterK (u:=plusU b u) S T K D A.milieu (principal K Z) (individual Z D) D' d x σ H a := by
 let s:= dawn D S; let H₀:= A.emits hb ((begins u a).trans hk); have HL:= H₀.leads N
 have hu:a+(plusU b u + plusU b u)≤k:= le_trans (by unfold tileC; omega) (show tileC (plusU b u) a ≤ k from (le_max_left ..).trans hk) -- unfold
 refine { atop:= fun _=> rfl, thick:=by omega, tilted:=fun w=> A.rates.preWard A.inspiration T (principal K Z) (drawing K P) A.bulk A.price (fifteen hb hk) A.port (inaugural K P Z B.ink) (D.before.wing w), stage:=?_, front:=?_ }
 · exact { home:= HL.crest, bound:= C.space, scale:= N.scale.us D.before.wing, clear:=C.clear,budget:=B.nonneg, gap:=C.rate }
 refine ⟨?_,fun i hi w j he=> A.rates.preWard A.inspiration T (Z i) (P i) A.bulk A.price (fifteen hb hk) A.port (B.ink i hi) (D.before.wing w) j he,fun i _ w=> (Z i).step_m (D.before.wing w)⟩
 exact ⟨B.wide, fun i hi w=> C.present i hi w.bindW,fun i hi w=> C.close i hi w.bindW,fun w=> C.apart w.bindW,fun i _ w=> (Z i).cap_b (essential R) _,fun i hi w=>launches K P Z B.ink i hi (D.before.page w), fun i _ w=> ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (ENNReal.ofReal_pos.mpr (s.hl w)).ne')) ENNReal.ofReal_ne_top,fun w=> (C.clear w.bindW).le⟩
lemma preserved (ht: K.accounts H≤a) : S.Preserved T (principal K Z) 1 (K.accounts H) p D x (plusU b u) L:= by
 let R':= A.emits hb ((begins u a).trans hk); let s:= principal K Z
 exact base_power S T K D A.milieu s (R'.leads N) (individual Z D) (cluster K P Z A B C N hb hk) ht
lemma enhanced (hn:K.accounts H+q ≤ a)(he:K.loss σ≤ (q:ℝ)): S.Preserved T (principal K Z) (fun w=> ENNReal.ofReal (S.ε w^ K.loss σ)) (K.accounts H+q) p D x (plusU b u) L:= by
 let R':= A.emits hb ((begins u a).trans hk);let t:=principal K Z
 exact spare_power S T K D A.milieu t (R'.leads N) (individual Z D) (cluster K P Z A B C N hb hk) hn he
variable {c':ℝ}
theorem funds (ht:K.accounts H≤a) (hx:0<c')(hg:S.cushion c' x)(he:e≤p)(hm:D.age≤J.age)(C₀:R.Endings L): Carry L (fun w=> ENNReal.ofReal (S.modifyErr (K.accounts H) b γ J w)) (fun w=> ‖ plotPT (R.clock (Page.opening M w)) (vital (TopF n w) (drawing K P w)) (K.accounts s) e-Ledger.Sky.note ((principal K Z).main (J.choose w) e 0)‖ₑ):=
 (A.emits hb ((begins u a).trans hk)).transmission (principal K Z) (drawing K P) (inaugural K P Z B.ink) N (preserved K P Z A B C N hb hk ht) hx hg he hm C₀
theorem gains (ht:K.accounts H+q≤a)(hp:K.loss σ≤q) (hx:0<c')(hg:S.cushion c' x)(he:e≤p)(C₀:R.Endings L): Carry L (retainErr S (K.accounts H) b γ (fun w=> ENNReal.ofReal (S.ε w^ K.loss σ))) (fun w=> ‖plotPT (R.clock (Page.opening M w)) (vital (TopF n w) (drawing K P w)) (K.accounts s) e‖ₑ):=by
 let t:=principal K Z;let F:= R.feeMarg; have hh := hinted R T t A.port (drawing K P) (inaugural K P Z B.ink); have hx' := A.emits hb ((begins u a).trans hk)
 have hv:= hx'.proper t (drawing K P) (inaugural K P Z B.ink) N (preserved K P Z A B C N hb hk (by omega)) hx hg
 apply Carry.mono (Cluster.there S T t hv (enhanced K P Z A B C N hb hk ht hp) (fun _=> ENNReal.ofReal_ne_top) F (R.year L C₀ u p) he); intro w
 exact le_of_eq (congr_arg (fun z:ℕ→ℝ=> ‖z e‖ₑ) (show plotPT _ _ _= S.vista T t F w from Coverage.poem _ _ _ _ _ hh R.learned w))
end Caps
end YM.RegulatorIR.Profiles
