import YM.RegulatorIR.Halo.Choir

/-! Mark Ward on perSrc directly by the repeat operation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{J I:Type}{c:ℝ}{k p m i a r s:ℕ} {W:Type}{M:W→ℕ}{n:Page M→Side}{S:Heir n G}
variable (H:Reel S) (T:S.Accounts)(Z:T.Report m)(w:W){L:Meter W}
variable (B: S.Supplies T L p k)(C: Aug.Amenities S L p k) (h':14≤k)(hp:H.Follows T)
variable (hc:Common H){U:W→Portrait G}(hU:∀ x,BasisT m s (U x) (Z.main (Page.opening M x)))
variable (j:ℕ)(h:j ≤ M w)
local notation "P0" => tele H T w
local notation "B0" => gazer H T Z w hp
local notation "C0" => Aug.sheet w j h
local notation "W0" => Page.mk w j h

lemma chord_s (A:Deck c I J)(u:ℝ→J→ℝ)(h:Ward.Lift u): chord A (vow u)= vow (fun t=>bridge A (u t)):=by ext1 i; unfold chord vow; rw [show (fun t=>bridge _ _ i)= ((fun _=>A.orient i)*(fun t=>u t (A.orbit i))) from rfl,tale_mul (f:=fun _=> A.orient i) contDiffAt_const (h _), tale_const]

variable {x y:ℝ→ Horizon G (n (Page.mk w j h))}
variable (Hx:ContDiffAt ℝ ∞ x 0)(Hy:ContDiffAt ℝ ∞ y 0)(Hs:Ward.reel_prop x y)

include Hx in
lemma rise (v:Side): cue H w j h v (signed (Sight.slab v) x)=chord (S.maps W0) (vow (peel x)):=by
 unfold cue; rw [chord_s (radar H w (C0 v)) _ (RangeR.lifts (wave (Sight.slab v) Hx)),chord_s _ _ (RangeR.lifts Hx)]; ext1 i; let z:=shiftE (S:=S) w (C0 v)
 apply congr_arg tale; ext1 t
 have hv(z') : bridge (radar H w (C0 v)) (peel (signed (Sight.slab v) x) t) z'=bridge (S.maps W0) (peel x t) z':=by rw [H.realms]; exact congr_fun (time_v _ (H.even W0) (H.phase W0) (x t)) z'
 change bridge (radar H w (C0 v)) _ (z i)= _; rw [hv]; unfold bridge; let A:= S.maps W0
 change A.orient (A.wind _ i)*peel x t (A.orbit (z i))= _
 rw [A.retreat,show A.orbit (z i)= _ from A.projected (.across (journey v)) i]; change 1*_ * _=_; rw [one_mul]

include Hx in
lemma world (p:ℕ): Aria H w j h (fun z=> signed (Sight.slab z) x) (chord (S.maps W0) (vow (peel x))) (p:=p):=by
 refine ⟨fun i=>wave _ Hx,?_,?_⟩
 · intro i hi x'; simp_rw [rise H w j h Hx]; exact tendsto_const_nhds
 intro i hi; obtain ⟨c,hc,h⟩:= noted x Hx p i hi; exact ⟨c,hc,fun k p=> h (Sight.slab k) p⟩

include H B C hp hU hc

def tern (i:Page M):=fun e r=>(S.maps i).scroll (Z.main i e r)
lemma rider {w:W}(j:ℕ)(h:j ≤ M w)(x:ℝ→ Horizon G (n (Page.mk w j h))){i:ℕ}(hi:i≤p): coeff i (reel (tern T Z ⟨w,j,h⟩) m x)= rhymeR (chord (S.maps ⟨w,j,h⟩) (vow (peel x))) (Z.main ⟨w,j,h⟩) m i:=by
 rw [rhyme_tube]; unfold rhymeR; apply sum_congr rfl; intro q hq; apply sum_congr rfl;intro r _
 apply chord_port; exact cusp_b H T Z w B C hp hc hU j h r _ (by have hr:=mem_antidiagonal.mp hq;omega)
include h' Hx Hy Hs
lemma mind : Squares p (reel (tern T Z W0) m x) (reel (tern T Z W0) m y):=by
 intro i h; rw [rider H T Z B C hp hc hU (w:=w) _ _ x h,rider H T Z B C hp hc hU (w:=w) _ _ y h]; exact harmony H T Z w B C h' hp hc hU _ _ (world H w j _ Hx p) (world H w j _ Hy p) (fun i=> waveV _ (H.even _) Hs) h
lemma grazed : Squares p (reel (Z.deviation W0) m x) (reel (Z.deviation W0) m y):=by
 have h:= hinted H T Z hp U hU; obtain ⟨q⟩:= Coverage.craved T Z H.docket _ h W0
 have ht:= Ward.RangeR.stamps (K:=H.stance W0) q Hx Hy Hs
 have hp':= mind H T Z w B C h' hp hc hU _ _ Hx Hy Hs
 have he u : reel (Z.deviation W0) m u=reel (Z.point W0) m u-reel (tern T Z W0) m u:=by rw [show Z.deviation W0=Z.point W0-tern T Z W0 from rfl]; unfold reel; rw [reel_split,map_sub]
 rw [he x,he y];apply Squares.sub _ hp';intro i hi; rw [← ht]
end YM.RegulatorIR.Halo
