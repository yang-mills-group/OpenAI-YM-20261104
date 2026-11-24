import YM.RegulatorIR.Gain.Orbits

/-!
# Path approximating on replicas; Ward for any bounded ✓

Qualitative point-cost after primitive/copy control for fixed finite horizon.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Gain
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Halo Halo.Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {X:Type} {f:Side}{p m s e k:ℕ}

-- native generator signed site convention.
def violetO (A: Horizon G f)(K:Site f→ G.Color) (i:OEdge f): Trip G :=(A i,K i.val.1,K (i.val.1+step i.val.2))
def current (A: Horizon G f)(K:Site f→ G.Color) (t:ℝ): Horizon G f:=fun i=> crest (violetO A K i) t
lemma current_space (A: Horizon G f)(K:Site f→G.Color) :ContDiffAt ℝ ∞ (current A K) 0:=contDiffAt_pi.mpr fun _=>crest_smooth _
lemma current_event (A:Horizon G f){K:Site f→G.Color}(h:EvenSite K) : reel_prop (current A K) (fun _=>A):=by
 filter_upwards [eventually_all.mpr fun z=>signal (violetO A K z)] with t ht;let k(a:Site f):= G.lieExp (t • K a)
 refine ⟨k,site_orbs h t,?_⟩; ext1 i; rw [goat_at]; exact ht i

abbrev BEdge (G:Gauge) := Edge Cover → G.Color

def violet (A:BEdge G)(σ:Cover→G.Color)(e: Edge Cover) : Trip G := (A e,σ e.1,σ (e.1+step e.2))

def shadowU (A:BEdge G)(σ:Cover→ G.Color)(t:ℝ)(i:Foot G):ℝ:= crest (violet A σ i.1) t i.2
def hue (A:BEdge G) (i:Foot G):= A i.1 i.2

variable (A:BEdge G)(σ:Cover→ G.Color)
section Ball
lemma sing_price (i:ℕ)(C:ℝ) : ∃ v:ℝ≥0∞,v ≠ ⊤ ∧∀ x:Trip G,‖x‖ ≤ C → ∀ j:G.ColorIndex, ‖song G i j x‖ₑ ≤ v:=by
 let f:=song G i; have hp(j:G.ColorIndex) :Continuous (f j):= by
    unfold f song jet; apply Continuous.const_mul; exact Continuous.comp (iteratedFDeriv ℝ (i+1) _ 0).coe_continuous (continuous_pi (fun _=>continuous_id))
 choose b hb using fun j:G.ColorIndex=> (isCompact_closedBall 0 C).exists_bound_of_continuousOn (hp j).continuousOn
 refine ⟨univ.sup fun i:G.ColorIndex=> ENNReal.ofReal (b i), ne_of_lt (Finset.sup_lt_iff (by simp)|>.mpr fun i _=> ENNReal.ofReal_lt_top),?_⟩
 intro x hx j; rw [← ofReal_norm]; apply le_trans _ (Finset.le_sup (f:=fun i:G.ColorIndex=>ENNReal.ofReal (b i)) (mem_univ j)); apply ENNReal.ofReal_le_ofReal; exact hb j x (mem_closedBall_zero_iff.mpr hx)
end Ball

variable (h:4≤f.val)(he:Even f.val)
abbrev fields (z:Side) : ℝ → Horizon G (rep f z):=fun _=> track z h A
abbrev eyes (z:Side) := current (track z h A) (dropV z h σ)
include he
lemma eyes_up (z:Side)(i:Edge Cover)(h₁:inside z i.1)(h₂:inside z (i.1+step i.2)) (j:G.ColorIndex) : (fun t:ℝ=>fire (eyes A σ h z t) (around _ (deep f z i)) j)=ᶠ[𝓝 0] fun t=> shadowU A σ t (i,j):=by
 let D:= dropV z h σ;let Q:=track z h A; let A₀:= violet A σ i
 let t:= around (rep f z) (deep f z i);let y:= index t; have hf := track_link z h A i h₁
 have hg:D t.1=σ i.1:= dropV_eq z h σ i.1 h₁
 have hs:D (t.1+step t.2)=σ (i.1+step i.2):=by
    change D (swim f z i.1+Lattice.step i.2)= _
    rw [show swim _ _ _+_= swim f z (i.1+step i.2) from ?_]; exact dropV_eq z h σ (i.1+step i.2) h₂
    unfold swim; rw [← add_assoc,map_add,map_add,map_add,wrap_step]
 rcases eR_spec t with hv|hv
 · have hp:y.val=t:=hv;have hx:violetO Q D y=A₀:=by
      have hh: Q y=fire Q t:= by rw [←hp,fire_at];
      unfold violetO A₀;rw [hp,hg,hs,hh,show fire Q t=A i from hf];rfl
   filter_upwards with u; change fire _ t j= _; rw [← hp, fire_at];change crest _ _ _=_;rw [show violetO Q D y=A₀ from hx]; rfl
 have hv' : y.val=reflect t:=hv
 have hw : Even (rep f z).val:=he.mul_left _
 have hh:D (-(t.1+step t.2))=D (t.1+step t.2):= dropV_tag z h σ _
 have ht:D (-t.1)=D t.1:= dropV_tag z h σ _
 have ha:Q y= -A₀.1:=by rw [← fire_at Q y,hv',fire_swaps Q hw]; exact congr_arg Neg.neg hf
 have hq: violetO Q D y=(-A₀.1,A₀.2.2,A₀.2.1):=by unfold violetO; rw [ha,hv']; dsimp only [Orb.reflect]; rw [sub_add_cancel,show -t.1-step t.2= -(t.1+step t.2) by abel, hh,ht,hg,hs]; rfl
 filter_upwards [crest_rev A₀] with u hu; change fire _ t j= _
 have hh:= fire_at (eyes A σ h z u) y; rw [hv',fire_swaps _ hw _] at hh;rw [← neg_neg (fire _ t), hh]; change (-crest (violetO Q D y) u) j= _;rw [hq,hu,neg_neg];rfl

omit he

def boundedC (x:X→G.Color):Prop:= ∃ c:ℝ,0≤ c ∧ ∀ i, ‖x i‖≤c
namespace Crew
variable {A σ} (Hx : boundedC A) (Hy : boundedC σ)
include Hx
lemma feelings : Full (fun z=> vow (peel (fields A h z))) p:=by
 obtain ⟨d,hd,hv⟩:= Hx
 intro i hi; refine ⟨ENNReal.ofReal d, ENNReal.ofReal_ne_top,?_⟩
 rintro z ⟨u,j⟩; let x:= track z h A u
 change ‖coeff i (tale (fun _=> x j))‖ₑ ≤ _;rw [tale_const,PowerSeries.coeff_C]; split
 · rw [← ofReal_norm]; apply ENNReal.ofReal_le_ofReal; exact (PiLp.norm_apply_le x j).trans (track_bill z h A hd hv u)
 simp
include Hy
lemma lashes : Full (fun z=> vow (peel (eyes A σ h z))) p:=by
 obtain ⟨d,hd,hv⟩:=Hx;obtain ⟨c,hc,hq⟩:=Hy
 intro i hi; obtain ⟨C,hP,Hs⟩:= sing_price (G:=G) i (max d c); refine ⟨C,hP,?_⟩
 rintro v ⟨u,j⟩; let f:= violetO (track v h A) (dropV v h σ) u
 change ‖coeff i (routeS G j f)‖ₑ≤ _;rw [song_jet]; apply Hs _ _ j
 unfold f violetO; simp only [Prod.norm_def];apply max_le (le_trans (track_bill v h A hd hv u) (le_max_left ..)); exact le_trans (max_le (drop_bill v h σ hc hq _) (drop_bill v h σ hc hq _)) (le_max_right ..)
end Crew

section Aura
variable {W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G} (R: Reel S) (w:W) (j:ℕ)(hk:j ≤ M w)
local notation "r0" => (Page.mk w j hk)
local notation "r" => n r0
local notation "a" => R.deep r0 -- quotPrecheck?
local notation "H" => Aug.sheet w j hk
def stage (z:Side) (x:ℝ→Horizon G (big w n (Aug.sheet w j hk z))) := cue R w j hk z x
lemma staged (z:Side) (x:ℝ→ Horizon G (big w n (Aug.sheet w j hk z)))(g:ContDiffAt ℝ ∞ x 0) (b: Foot G) :
 stage R w j hk z x b= tale (fun t=> fire (x t) (around _ (deep r z b.1)) b.2):=by
 let f:= H z; unfold stage cue; rw [chord_s _ _ (RangeR.lifts g)]; rw [Function.comp_apply]; unfold vow; apply congr_arg tale;ext1 t; unfold Halo.shiftE; rw [R.realms]; exact firebrand (Sight.refined R w f) (Sight.context R w f) (x t) b.2 _
lemma ariaB (p:ℕ)(Hx: boundedC A) : Aria R w j hk (X:=fun z=>fields A (R.deep r0) z) (vow (fun _=> hue A)) (p:=p):=by
 let t:= R.deep r0
 refine ⟨fun _=>contDiffAt_const, ?_,Crew.feelings t Hx⟩
 intro i _ v; refine tendsto_const_nhds.congr' ?_;filter_upwards [included v.1.1] with z hz;change coeff i (tale (fun _=> _))=coeff i (stage _ _ _ _ _ _ _)
 rw [staged R _ _ _ _ _ contDiffAt_const]
 apply congr_arg; apply congr_arg;ext1 s; exact congr_arg (fun y:G.Color=>y v.2) (track_link z t A v.1 hz).symm
lemma ariaF (p:ℕ)(Hx: boundedC A)(Hy:boundedC σ) :Aria R w j hk (X:=fun z=> eyes A σ (R.deep r0) z) (vow (shadowU A σ)) (p:=p):=by
 let t:=R.deep r0
 refine ⟨fun v=>current_space (track v t A) (dropV v t σ), ?_, Crew.lashes t Hx Hy⟩
 intro i _ v; refine tendsto_const_nhds.congr' ?_
 filter_upwards [included v.1.1,included (v.1.1+step v.1.2)] with z h₁ h₂
 let g:=eyes A σ t z
 change _=coeff i (stage R w j hk z g v)
 rw [staged R w j hk z g (current_space (track z t A) (dropV z t σ))]
 let v':Trip G:= violet A σ v.1
 let U: G.Color→L[ℝ] ℝ:= PiLp.proj 2 (fun _: G.ColorIndex =>ℝ) v.2
 have ht : ContDiffAt ℝ ∞ (fun u=> shadowU A σ u v) 0:= U.contDiff.contDiffAt.comp _ (crest_smooth v')
 exact congr_arg (fun y=>PowerSeries.coeff i y) (tale_eq ht (eyes_up A σ t (R.even _) z v.1 h₁ h₂ v.2)).symm

variable {L :Meter W}
theorem plasma (T:S.Accounts)(Z:T.Report m)(B: S.Supplies T L p k)(C: Aug.Amenities S L p k)(H0:14≤k)(E:R.Follows T) (P: Common R) {U:W→ Portrait G} (hU:∀ i,BasisT m s (U i) (Z.main (Page.opening M i)))(HA:boundedC A)(HF:boundedC σ){e:ℕ}(hp:e ≤ p): rhymeR (vow (shadowU A σ)) (Z.main r0) m e= rhymeR (vow (fun _=>hue A)) (Z.main r0) m e:= harmony R T Z w B C H0 E P hU j hk (ariaF A σ R w j hk p HA HF) (ariaB A R w j hk p HA) (fun z=>current_event _ (dropV_tag z (R.deep r0) σ)) hp
end Aura
end YM.RegulatorIR.Gain
