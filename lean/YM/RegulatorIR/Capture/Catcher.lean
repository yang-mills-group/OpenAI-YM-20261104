import YM.RegulatorIR.Capture.Tiles

/-!
# Sweeping from an intermediate grouped stage to terminal output grade zero

Normalized center averages. *Positive input* supports, full ranks, threshold
pruning not internal. The scalar stop only reads h=0. No correlation for
captured positive sector asserted. No commutation with ν or phase averages. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Capture
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}

variable {S:Heir n G} (R: Reel S)(T:S.Accounts)(Z:(portraitR T).Report m)
private lemma intPaid {Y:Room→Orders X}{l:ℝ}(s:Store Y (Metric.closedBall 0 l) p)(φ: Room→ℝ)(hp:Continuous φ)(hl:0<l)(he:e ≤ p) (x:Tuple X j) :
 IntegrableOn (fun v=> φ v* Y v e j x) (seatX l):=by
 have ht: IntegrableOn (fun x' => ∑ i∈s.topP,(φ x'*s.feel i x')*s.leg i e j x) (seatX l):= integrable_finsetSum _ fun i hi=>(seatIn ((hp.mul (s.kept i hi)).mul continuous_const) hl.le)
 apply IntegrableOn.congr_fun ht _ (seen ..); intro v hv; dsimp only; rw [s.sense _ (seatCaps hl.le hv) _ he]; simp_rw [Finset.sum_apply, Finset.mul_sum]; apply sum_congr rfl;intro i hi;exact mul_assoc ..

def weighsC (l:ℝ)(P:Room→Orders X)(φ:Room→ℝ): Orders X:= fun i j z=> weighT l fun x=>φ x* P x i j z
private lemma scores {l:ℝ}{Y:Room→Orders X}(hl:0<l)(s:Store Y (Metric.closedBall 0 l) p)(φ: Room→ℝ)(h:Continuous φ) e (ht:e≤p) : weighsC l Y φ e= (∑ i∈s.topP, weighT l (φ*s.feel i) • s.leg i) e:=by
 ext1 j;ext1 z
 unfold weighsC; rw [seatCongr (g:=fun w=> ∑ i∈s.topP,(s.leg i e j z) *(φ w * s.feel i w)) _ ?h]; case h=>
    intro v hv;rw [s.sense _ (seatCaps hl.le hv) e ht];simp_rw [Finset.sum_apply,mul_sum];apply sum_congr rfl;intro i _;simp only [Pi.smul_apply, smul_eq_mul];ring
 rw [seatSum];swap;exact fun i hi=> seatIn (continuous_const.mul (h.mul (s.kept i hi))) hl.le
 simp_rw [Finset.sum_apply,seatScale]; apply sum_congr rfl;intro i _; exact mul_comm ..

variable (G₀:Milieu S T k p L)
include G₀ in
lemma covers_step (w:Flap M){F:Room→Orders (Foot G)}(s:Store F (Metric.closedBall 0 (S.l w.prev)) p)(φ:Room→ℝ)(h:Continuous φ)(he:e ≤ p) : (S.frames w).each m (T.bulk w.prev) (weighsC (S.l w.prev) F φ) e= weighsC (S.l w.prev) (fun x=>(S.frames w).each m (T.bulk w.prev) (F x)) φ e:=by
 rw [survivesP _ _ (scores (S.hl _) s φ h) he, dividends G₀ w s.topP (fun i=> weighT (S.l w.prev) (φ*s.feel i) • s.leg i) (fun i hi=>scalePrice (s.sure i hi) _) he, scores _ (s.comes G₀ w m) φ h _ he,Finset.sum_apply];swap;exact S.hl _
 apply sum_congr rfl;intro i _; rw [homogenous]; rfl

-- exact capture sample at b

def collected (w:Page M): Sample (Foot G):= fun φ=>weighsC (S.l w) (fun x=> Z.main (leafX w x)) fun x=> φ ((S.l w)⁻¹ • x)

def rebroadcast (w:Flap M)(U:Sample (Foot G))(m:ℕ) : Sample (Foot G):= fun φ=> let L:=(R.steps w).patch.L; tally L 0 • ∑ i:Site L, (S.frames w).each m (T.bulk w.prev) (rebaseO (Lattice.lift i) (U (calling L φ i)))
-- propagate on all older steps, grade zero. scalar operator not acquiring L.

def catcher (D:Choice M): Page D.after.spans → Sample (Foot G) := seriesC (X:=fun _=> Sample (Foot G)) (fun w=> collected T Z (D.choose w)) (fun i v=> rebroadcast R T (D.after.wing i) v m)

variable (P:Passage R)(he:Common R)(hv:R.Follows T)
variable (H:∀ w l,Nonempty (Store (fun x=>Z.main (leafX w x)) (Metric.closedBall 0 l) p))
variable (HX:∀ i x t, swing Z i x t)
private lemma addressF (t: Side)(l:ℝ)(hl:0<l) (v:Site t) (x:Room): ((l*t.val)⁻¹:ℝ) • (location t l v+x)= (display t)⁻¹ • slide 1 (Lattice.lift v)+(display t)⁻¹ • (l⁻¹ • x):=by ext1 i; simp [location, display]; field_simp
include H HX G₀
lemma captured_step {φ:Room→ℝ}(h:Continuous φ)(w: Flap M)(hi:e≤p) : collected T Z w.next φ e= rebroadcast R T w (collected T Z w.prev) m φ e:=by
 let l:= S.l w.prev
 let L:=(R.steps w).patch.L
 let a:= display L; have ha: 0<a:=by unfold a display; positivity
 let Q:= (S.frames w).each m (T.bulk w.prev)
 let U x:= Z.main (leafX w.prev x)
 let V x:= Z.main (leafX w.next x)
 have ht:S.l w.next=l*L.val:= scaledCard ..
 have hl:0<l:= S.hl _
 let u:= (H w.prev l).some; let v:=(H w.next (l*a)).some
 ext1 i;ext1 z
 let f:= fun x=>φ ((S.l w.next)⁻¹ • x) * V x e i z
 have hs(y): Q (U y)=V y:= Z.step_m (turnX w y)
 change weighT (S.l w.next) f= (tally L 0 • (∑ i: Site L,Q (rebaseO _ _))) _ _ _
 rw [ht,meanTiles L hl (R.steps w).patch.odd_side];swap;exact intPaid v _ (by refine h.comp (f:=fun x:Room=> (S.l w.next)⁻¹ • x) ?_;fun_prop) (by positivity : 0<l*a) hi z
 simp_rw [Pi.smul_apply,Finset.sum_apply]; simp only [smul_eq_mul]
 apply congr_arg;apply sum_congr rfl
 intro y _;let t:= Lattice.lift y; let g:= calling L φ y
 let v:=fun x:Room=>g (l⁻¹ • x); have hh: Continuous v:= by unfold v g calling gaze;fun_prop
 change weighT l (fun a=>f (location L l y+a))= Q (rebaseO (Lattice.lift y) (collected T Z w.prev g)) e i z
 unfold f
 let B(u':Room):= rebaseO t (U u')
 have hV (p: Room) : V (location L l y+p)= Q (B p):=by
   rw [← hs]; apply congr_arg; ext1 i;ext1 j; exact Echos.only (HX w.prev t p i j)
 simp_rw [hV]
 -- now repr Q on integrated B. need Stock for rebase.
 have hs' : Store B (Metric.closedBall 0 l) p:= { u with leg:= fun x=> rebaseO t (u.leg x), sure:=fun i hi=>echoBill t _ (u.sure i hi), sense:=fun x h i hv=>by dsimp only [B]; ext1 j; unfold rebaseO; rw [show U x i=_ from u.sense x h i hv]; simp_rw [Finset.sum_apply]; ext1 z;simp [echo,Finset.sum_apply] }
 rw [show rebaseO _ (collected T Z w.prev g)=weighsC l B v from rfl];change weighT l _=(S.frames w).each _ _ _ _ _ z
 rw [covers_step T G₀ w hs' v hh hi]; unfold weighsC; apply congr_arg (weighT l); ext1 A;apply congr_arg (fun u=>u * _);rw [ht,addressF _ _ hl];rfl

lemma captured : ∀ w: Page D.after.spans,∀ (φ:Room→ℝ),Continuous φ→ ∀ e≤p, catcher R T Z D w φ e=collected T Z (D.after.page w) φ e:=by
 refine Page.proves (fun w _ _ _ _=>rfl) ?_; intro w hx φ h e hi;unfold catcher; rw [laterC]; change rebroadcast R T (D.after.wing w) _ m φ e=collected _ _ (D.after.wing w).next _ _; rw [captured_step R T Z G₀ H HX h (D.after.wing w) hi]; let L:=(R.steps (D.after.wing w)).patch.L
 unfold rebroadcast; simp only [Pi.smul_apply,Finset.sum_apply];apply congr_arg; apply sum_congr rfl;intro v _; apply survivesP _ _ _ hi
 intro i h';let f:=calling L φ v
 have hv : Continuous f:=by unfold f calling gaze;fun_prop
 ext1 j; unfold rebaseO;congr 1; exact congr_fun (hx f hv i h') j
end YM.RegulatorIR.Capture
