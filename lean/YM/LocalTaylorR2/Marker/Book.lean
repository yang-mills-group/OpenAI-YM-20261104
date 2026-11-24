import YM.LocalTaylorR2.Marker.Sigil
import YM.LocalTaylorR2.License
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
variable {k l:ℕ} (p:H.ThinP)
def heeded (χ:Chi)(l:ℕ) (q:Orders l) (V:Config G c):=if lush M H p then convolve (U:=partners M p.val) q (fun i=> episode H χ p.val (team M H (p:=p) i) V) else 0
def dial (χ:Chi) (p:H.ThinP) (q:Orders l) (V:Config G c):=if q=perch l then libs M H χ V p-∑ t∈univ.erase q,heeded M H p χ l t V else heeded M H p χ l q V
lemma recovers (χ:Chi) (l:ℕ) (V:Config G c):
    libs M H χ V p=∑ q:Orders l,dial M H χ p q V:=by
  let z:=perch l; rw [←add_sum_erase _ _ (mem_univ z),dial,if_pos rfl]; apply Eq.symm
  have he : ∑ q∈univ.erase z,dial M H χ p q V=∑ q∈univ.erase z, heeded M H p χ l q V:= sum_congr rfl (fun q h=>if_neg (ne_of_mem_erase h))
  rw [he]; ring
lemma silent (hv:¬lush M H p) (q:Orders l) (hp:q≠perch l) : dial M H χ p q=fun _=>0:=by funext V; unfold dial heeded; rw [if_neg hv, if_neg hp]
lemma charged (hv:¬lush M H p) (l:ℕ): dial M H χ p (perch l)=fun V=>libs M H χ V p:=by funext V;simp [dial,heeded,hv]
lemma lull (he:¬treads M H p) (q:Orders l) : dial M H χ p q=fun _=>0:=by
  have h:¬lush M H p:=fun h=>he h.1
  by_cases hv:q=perch l
  · rw [hv,charged M H p h];exact funext fun V=> halt M H _ χ he
  exact silent M H p h q hv

variable {b D K B v r w q' θ c' ρ ζ : ℝ} (N:Captain H j C' d v w A b r B q' (n+j) χ) (U:StoresR2 H j v d A D k x' n χ)(hr:Tinted G x K d o.a L χ j)
set_option quotPrecheck false
local notation "Z"=>N.conduit
local notation "d0"=> jewelDebt M Q L x

include N
lemma realize (hp:lush M H p)(q:Orders l) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V:E→ Config G c) (t:E) (he:Mode V t j v) (ht:Healthy (Pressure.temp x) (H.smallAt p) (V t)) : dial M H χ p q ∘ V=ᶠ[𝓝 t] heeded M H p χ l q ∘ V:= by
  by_cases hq:q=perch l; swap; · exact Eventually.of_forall fun _=> if_neg hq
  have hh:= episodeSum (H0:=fun F X w=>squad M X H _ w) N.oboe p.2.2 he (H:=H) (heroKept M H hp.1) (g:=team M H (p:=p) (k:=l)) (fun i=>teamKept M H hp.1 i) ht
  filter_upwards [hh] with y hy; dsimp only [Function.comp_apply,dial]; rw [if_pos hq]; apply sub_eq_iff_eq_add.mpr
  rw [show heeded M H p χ l q (V y)+ (∑ t∈ univ.erase q,heeded M H p χ l t (V y))= _ from add_sum_erase _ (fun t=> heeded M H p χ l t (V y)) (mem_univ q),income M H _ _ hp.1 hp.2]; change _=∑ t: Orders l, heeded M H p χ l t (V y)
  simp_rw [heeded,if_pos hp]; rw [Candle.collects]; exact hy

section aerial
variable (h : 1≤betaF G x L) (hζ:0≤ζ) (hp:1≤ρ) (hy:1≤y) (hI:LocalBookingsR2 ζ c' N.conduit) (hY:Herd H N.conduit A B (n+j)) (hθ:1≤θ)(he:Charge.Allows l j θ)
    (hs:ρ*c'≤1) (hq: ρ^(l+1) ≤ betaF G x L^ζ) (hh:betaF G x L^ζ ≤ Real.exp (Q.mark L μ x))

abbrev prismCash (x' D K r:ℝ) (l j:ℕ):ℝ:=x'*(1+D+speedS K r l)^j
def toll (p₀:Paint (partners M p.val) l)(x' D K y θ:ℝ):ℝ:=(y*jewel M Q L x)*forge (Z) θ p₀*prismCash x' D K r l j*(1+H.shapeW p.val)^(n+j)
-- grade normalized to `dust` no dividing out zero weight.

def period (x' D K y θ:ℝ)(u:Orders l):ℝ:= if lush M H p then convolve (U:=partners M p.val) u (fun q=> toll M H p N q x' D K y θ) else if u=perch l∧ treads M H p then B*(y*persona M H C' (Z).flair 0 (n+j) 0 p.val) else 0
include hY hy
omit hY in
lemma tollN (q:Paint (partners M p.val) l) (hθ:1≤θ)(ht:Tinted G x K d o.a L χ j) (hU:0≤ x')(hD:0≤D): 0≤ toll M H p N q x' D K y θ:= by
  have hr:= N.conduit.active; have hT:= ht.salt; have h:= forgeN (Z) hθ q; have hp:= (dew M H).1; have he:= H.positive_volume p.val; unfold toll prismCash speedS; positivity
omit hY in
lemma periodN (u:Orders l)(hθ:1≤θ)(ht:Tinted G x K d o.a L χ j) (hU:0≤ x')(hD:0≤D): 0≤ period M H p N x' D K y θ u:=by
  unfold period; split
  · exact Finset.sum_nonneg fun _ _=>tollN M H p N hy _ hθ ht hU hD
  split
  · exact mul_nonneg N.balance (mul_nonneg (zero_le_one.trans hy) (earned M H _ _ (Z).fares ..))
  exact le_rfl
omit N in
abbrev refund (M:Leaf R)(Q:YM.ConnectedActivityE6.Target G P)(L:Side)(x y:ℝ):ℝ:= jewelDebt M Q L x/y
local notation "K!" => refund M Q L x y
omit hy in
lemma letterSafe (q:Orders l) : Items H p (dial M H χ p q):=by
  have hv:= debtor M H hY p.2.2
  have ht(q:Orders l): Items H p (heeded M H p χ l q):=by
    unfold heeded; by_cases he:lush M H p; swap; · simp_rw [if_neg he]; exact ⟨fun _ _=>rfl,measurable_const,fun _ _ _=>rfl⟩
    simp_rw [if_pos he]; have hm (q:Paint (partners M p.val) l):= episodeSites (p:=p.val) H (teamKept M H he.1 q) χ
    exact ⟨fun U V=> Finset.sum_congr rfl (fun i _=> (hm i).2.2 U V),Finset.measurable_fun_sum _ (fun i _=> (hm i).1), fun U V h=> Finset.sum_congr rfl (fun i _=> (hm i).2.1 _ _ h)⟩
  unfold dial; by_cases he:q=perch l; swap; · simp_rw [if_neg he]; exact ht _
  simp_rw [if_pos he]
  exact ⟨fun U V=> congr_arg₂ (·-·) (hv.2.2.1 U V) (Finset.sum_congr rfl fun i _=> (ht i).1 U V), hv.2.1.sub (Finset.measurable_fun_sum _ fun i _=> (ht i).2.1),fun U V h=> congr_arg₂ (·-·) (hv.1 _ _ h) (sum_congr rfl fun i _=> (ht i).2.2 U V h)⟩

include h hζ hp hy hI U hr hθ he hs
lemma sustainsO (q:Orders l) (V:Config G c) (hv: Healthy (Pressure.temp x) (H.smallAt p) V): Ore V (dial M H χ p q) v ((K!)*period M H p N x' D K y θ q) j:=by
  unfold period; have hl:0< y:=zero_lt_one.trans_le hy
  split
  next h0=>
    have ht:c'≤1:=(le_mul_of_one_le_left (budget_nonneg (hI.leases.hit 0)) hp).trans hs
    let f q:= episode H χ p.val (team M H (k:=l) (p:=p) q)
    have hk: (K!)*(y*jewel M Q L x)=M.weight:=by rw [(dew M H).2.2]; unfold refund; field_simp
    have hh(q':Paint (partners M p.val) l): Ore V (f q') v ((K!)*toll M H p N q' x' D K y θ) j:=by
      have hm : 0≤ speedS K r l:= by unfold speedS; have h:=hr.salt; have hb:=N.conduit.active; positivity
      have hq:= Charge.holds U _ (mul_nonneg M.profit (forgeN N.conduit hθ q')) hm _ (team_sees M H hI hr q' h0.1 he (slack _ hI h hζ ht))
      unfold toll; rw [← mul_assoc (K!),← mul_assoc (K!),← mul_assoc (K!),hk]
      exact episodeCost H N.oboe p.2.2 (teamKept M H h0.1 q') hq V hv
    intro E _ _ _ W s hw hW; apply Brush.shimmy _ (realize M H p N h0 q E W s hW (hw.symm ▸ hv))
    unfold heeded convolve; simp_rw [if_pos h0,Finset.mul_sum]; exact Brush.spree _ (fun p v=> f p (W v)) _ zero_le_one fun i _=> hh i E W s hw hW
  next hF=>
    split
    next hv'=> rw [hv'.1,charged M H p hF]; rw [mul_left_comm B, ← mul_assoc (K!), show (K!)*y=jewelDebt M Q L x from (div_mul_cancel₀ _ hl.ne')]; exact (debtor M H hY p.2.2).2.2.2.2 V hv
    next hx=> rw [mul_zero, show dial M H χ p q=(fun _=>0) from by
                by_cases hv:treads M H p
                · exact silent M H p hF q fun h=> hx ⟨h,hv⟩
                exact lull M H p hv q]
              intro E _ _ _ U x h hp; exact (Brush.certified zero_le_one 0).climb (norm_zero.le) le_rfl
end aerial
end YM.LocalTaylorR2.Marker
