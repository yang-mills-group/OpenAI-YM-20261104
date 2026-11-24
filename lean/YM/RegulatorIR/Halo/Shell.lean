import YM.RegulatorIR.Halo.Lunar

/-!
# Replica location costs and cover source at fixed length

Deliberately not use repeated gain (`L`), develop for a single page, copies of
an original gauge+operators setup only. Later gauge analysis permits arbitrary
depth bounds of a stronger type. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo.Aug
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Sight Uniform Spatial
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side}{p w s m i r a:ℕ}
variable {S:Heir n G} (H: Reel S)(T:S.Accounts)(Z:T.Report m) {L:Meter W}
-- root width neutral

def centre (S:Heir n G)(w:W)(i: Side): Room:=Motion.loc (S.P w) (.across (journey i)) 0
lemma heatC (S:Heir n G)(w:W)(i: Side): centre S w i (0:Axis)=(S.P w)*i.val:=by unfold centre Motion.loc; simp [journey]
lemma core (S:Heir n G)(w:W)(i: Side) : S.P w*i.val≤ Spatial.singular ((width (S:=S) w) i) (centre S w i):=by -- Sense replace
 let P:= S.P w;let A:= width (S:=S) w i/2;let c:=centre S w i
 let f:= nearest A c; let v:= P*i.val;have hP:0<P:= S.hp w;have hx:A=v*2:=by unfold A v width P Sight.slab; simp;ring
 have hp:=i.property; have he:0<v:= by unfold v; positivity
 refine le_trans ?_ ((pi_norm_le_iff_of_nonempty (c-slide A f)).mp le_rfl 0)
 simp only [Pi.sub_apply, slide_apply, Real.norm_eq_abs]; rw [show c 0=v from heatC ..,hx];change v ≤ |v-v*2*(f 0:ℤ)|
 by_cases h: (f 0:ℤ) ≤ 0
 · refine le_trans ?_ (le_abs_self _); have hh:(f 0:ℝ) ≤ 0:=by exact_mod_cast h
   nlinarith
 refine le_trans ?_ (neg_le_abs _);have hh:(1:ℤ)≤ f 0:= by omega
 have hx:(1:ℝ)≤ (f 0:ℝ):=by exact_mod_cast hh
 nlinarith

-- weight conversions, Post cost base translation
variable (w:W)
def debt (p:Side):ℝ≥0∞:= ENNReal.ofReal (((p.val:ℕ):ℝ)⁻¹)
lemma debtCost (j:ℕ)(h:j<M w) : let g:= (known H w j h).insideRoom (fun _=> delay (S:=S) w j h) (fun _=> S.hl _); Carry light debt fun u=> ((1:Side→ℝ≥0∞) u)*(g.toll (centre S w) 1 u)⁻¹:=by
 intro g; let l:= delay (S:=S) w j h;let P:= S.P w;let C:=l/P; have hl:0<l:= S.hl _;have hP:0<P:=S.hp w;refine ⟨_,Poly.standard _ (show ENNReal.ofReal C≠ ⊤ from ENNReal.ofReal_ne_top),?_⟩
 intro u; dsimp only; rw [Pi.one_apply,one_mul,Post.toll,Tariff.amount,pow_one]; let b:= singular (width (S:=S) w u) (centre S w u); have hb:0≤ b:= singular_nonneg ..
 change (ENNReal.ofReal (1+b/l))⁻¹ ≤ ENNReal.ofReal C*_ ;let r:ℝ:=u.val
 have hr:0<r:=by unfold r; exact_mod_cast u.property
 change _ ≤ ENNReal.ofReal C* ENNReal.ofReal r⁻¹;rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by dsimp only [C]; positivity)];
 apply ENNReal.ofReal_le_ofReal; rw [← div_eq_mul_inv]; apply le_trans (b:=(P*r/l)⁻¹) ;
 · apply inv_anti₀ (by positivity); exact le_trans (div_le_div_of_nonneg_right (core S w u) hl.le) (le_add_of_nonneg_left zero_le_one)
 exact le_of_eq (by unfold C; field_simp)

-- exact width orientation with arc translate

lemma root_shape (j:ℕ)(h:j ≤ M w)(i:Side) (z:Tuple (Foot G) r)(a:ℕ) : ((lpost H w j h).rooted (centre S w) a i).width (onPath (shiftE (S:=S) w (sheet _ _ h i)) z)= (S.census.rooted (fun _=>0) a (⟨w,j,h⟩:Page M)).width z:=by
 let U:= sheet w j h i;let V:= Sight.ray w U; let f:= shiftE (S:=S) w U
 let A:= (lpost H w j h).rooted (centre S w) a i;let B:= S.census.rooted (fun _=>0) a V
 have hz (x): ((lpost H w j h).deck i).pos (f x)=Motion.loc (S.P w) (.across (journey i)) ((S.maps V).pos x):=by
    have hx:= (S.maps V).displaced (Motion.across (journey i)) x
    calc
      _ = (S.maps V).pos (f x):= by change (radar H w U).pos _=_; rw [H.realms];rfl
      _ = _:= hx
 change A.width (onPath f z)=B.width z
 unfold Premium.width Tariff.diameter
 let T:= (lpost H w j h).cone a i; let T':= S.census.cone a V
 have hp (u v : Fin r) : T.road (onPath f z u) (onPath f z v)= T'.road (z u) (z v):=by
    let P:=S.P w
    apply congr_arg (Tariff.amount (S.l V) a)
    simp_rw [onPath, Function.comp_apply]; rw [hz (z u),hz (z v), Motion.cost_loc];rfl
 have hM (x:Fin r):A.mark (onPath f z x)=B.mark (z x):= by
    apply congr_arg (Tariff.amount (S.l V) a)
    simp_rw [onPath, Function.comp_apply]; rw [hz, centre,cost_loc];rfl
 change (((⨆ u, ⨆ v, T.road (onPath f z u) (onPath f z v))⊔1)⊔⨆ u,A.mark (onPath f z u))= _ -- binder need explicit
 simp_rw [hp,hM];rfl
end YM.RegulatorIR.Halo.Aug
