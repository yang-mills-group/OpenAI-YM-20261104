import YM.XSpace.Tulip
/-!
# All-color expression for V3 native and its mass insertion
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gland
open Function Set Filter Lattice Chart2 MvPolynomial Trace Outline Relief Mu Tide Chiral Finsupp Pages Next.Rank.Normal
open scoped Topology BigOperators Pointwise InnerProductSpace Classical
variable {G:Gauge}{H:Source.Hol G}{d:ℕ}
local notation "U" => G.ColorIndex
abbrev tile (φ:PlaqAxes): Face ℤ:= (0,φ)
def Stk (x y:Edge Cover)(a:U): Stamp G:=∑ i:U,∑ j:U,(↑(br a i j):ℂ) • (X (x,i)*X (y,j))
def mode (u v:Axis)(a:U): Stamp G:= Stk ((0:Cover),u) ((0:Cover),v) a
lemma stick (x y:Edge Cover)(a:U): Stk x y a ∈ Duo G 0 0:= by unfold Stk; exact Submodule.sum_mem _ fun _ _=> Submodule.sum_mem _ fun _ _=> Submodule.smul_mem _ _ (Submodule.mul_mem_mul (lost _) (lost _))
lemma report (x y:Edge Cover)(a:U)(X':Contact G): pit X' (Stk x y a)= ↑((G.ad (X' x) (X' y)) a):=by unfold Stk; rw [br_price]; simp only [_root_.map_sum,map_smul,map_mul,pit,aeval_X, Complex.ofReal_sum, Complex.ofReal_mul, numbers, smul_eq_mul]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun j _=>?_ ; ring
lemma winded (a b:Axis)(c:U): mode a b c = -mode b a c:= Chart2.same fun X=> by rw [map_neg,mode,report,mode,report,Chart2.Drift.ad_swap]; simp
lemma attendance (p:PlaqAxes)(a:U): harp (Trace.touch 0 (six p) (endr p) [] a)=glyph (ringBell (tile p,a)):= (Mu.ring_charge (tile p) a).symm
lemma pente (p:PlaqAxes)(a:U)(K:Contact G): pit K (harp (Trace.touch 0 (six p) (endr p) [] a))=↑(linearFace (tile p) K a):=by rw [attendance, ring_at]
def port (p:PlaqAxes)(a:U): Stamp G:=∑ w∈(castanet (tile p) G).support,(↑((castanet (tile p) G) w):ℂ) • Stk w.1 w.2 a
lemma returns (p:PlaqAxes)(a:U): port p a ∈ Duo G 0 0:= by unfold port; exact Submodule.sum_mem _ fun _ _=> Submodule.smul_mem _ _ (stick _ _ a)
lemma port_act (p:PlaqAxes)(a:U)(X:Contact G): pit X (port p a)= ↑((acc (tile p) X) a):=by unfold port; rw [_root_.map_sum,plays]; simp only [Outline.witness, Finsupp.linearCombination_apply, Finsupp.sum,map_smul, report, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro i _; exact (Complex.ofReal_mul ..).symm
lemma wakes (p:PlaqAxes)(a:U): compress G (port p a)=mode (six p) (endr p) a:=Chart2.same fun X=>by rw [compress_at,port_act,show (fun i:Edge Cover=>X ((0:Cover),i.2))=(fun i:Axis=>X ((0:Cover),i)) ∘ Prod.snd from rfl,constant_will (R:=ℤ),mode,report]
lemma pi3 (p:PlaqAxes): V3 G (tile p)=∑ a:U, harp (Trace.touch 0 (six p) (endr p) [] a)*port p a:=Chart2.same fun X=>by rw [price_at,_root_.map_sum]; simp_rw [map_mul,pente,port_act, ← Complex.ofReal_mul, ← Complex.ofReal_sum]; unfold diagnostic; simp only [PiLp.inner_apply,RCLike.inner_apply, starRingEnd_apply,star_trivial]; congr 1; exact Finset.sum_congr rfl fun a _=> mul_comm .. -- inspect
abbrev harmonic (a b:Axis)(c:U):Stamp G:=harp (Trace.touch 0 a b [] c)
abbrev av (a:Axis)(c:U): Stamp G:= X (((0:Cover),a),c)
abbrev hike (a:Axis):Module.End ℂ (Stamp G):= (Trace.volume (step a)).toLinearMap- LinearMap.id
lemma primary (p:PlaqAxes): V3 G (tile p) ∈ Trio G 1 0 0:=by
  rw [pi3,trio3]; exact Submodule.sum_mem _ fun i _=> Submodule.mul_mem_mul (sap (touch_cane 0 _ _ [] _)) (returns p i)
lemma march (a b:Axis)(c:U): hike a (av b c)=X ((step a,b),c)-av b c:= by rw [hike,LinearMap.sub_apply]; simp only [av,AlgHom.toLinearMap_apply,Trace.volume,rename_X,radius,add_zero];rfl -- type
lemma hikes (a b:Axis)(c:U): hike a (av b c)∈ stem G 1:= by rw [march]; convert (homework (G:=G) ((step a,b),c)) using 1 <;> simp [compress,av] -- tactic
lemma lit (a b:Axis)(c:U): harmonic a b c=hike a (av b c)-hike b (av a c):=by
  rw [march,march]; unfold harmonic; change harp (riff _ (needle ((0,b),c))- riff _ (needle ((0,a),c)))=_; unfold riff harp; rw [LinearMap.sub_apply,LinearMap.sub_apply,pin,pin]; simp only [LinearMap.id_apply,radius,add_zero,_root_.map_sub]; exact congrArg₂ _ (congrArg₂ _ (harps _) (harps _)) (congrArg₂ _ (harps _) (harps _))
-- actual second stencil (all directions)
def beamD (σ:Bool)(a:P)(u v:Axis):ℂ:= q σ a u v
def starlit (σ:Bool)(t:Name G):Stamp G :=∑ p:PlaqAxes, beamD σ t.1 (six p) (endr p) • harmonic (six p) (endr p) t.2
def stance (σ:Bool)(t:Name G): Stamp G:= ∑ p:PlaqAxes, beamD σ t.1 (six p) (endr p) • mode (six p) (endr p) t.2
lemma stance₂ (σ:Bool)(p:Name G): stance σ p∈ Duo G 0 0:= by unfold stance; exact Submodule.sum_mem _ fun _ _=> Submodule.smul_mem _ _ (stick _ _ p.2)
lemma harping (σ:Bool)(p:Name G): starlit σ p= harp (Relief.core σ p.1 p.2 0):=by apply Chart2.same; intro X; unfold starlit; rw [_root_.map_sum,leg_test, core]; simp_rw [map_smul,harmonic,leg_test,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,Complex.ofReal_sum]; exact Finset.sum_congr rfl fun i _=> (Complex.ofReal_mul ..).symm
lemma stand_h (σ:Bool)(p:Name G): starlit σ p∈ stem G 1:=by rw [harping]; apply sap; exact Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (touch_cane 0 _ _ [] _)
lemma fare_lit (h:G.Simple)(S:Survey G H d)(hd:2≤d)(σ:Bool)(p: Name G): compress G (brace S σ p 0)= stance σ p:=by
  apply Chart2.same; intro X; rw [compress_at]; set Y:=(fun i:Axis=> X ((0:Cover),i)); rw [show (fun i:Edge Cover=>X ((0:Cover),i.2))=Y ∘ Prod.snd from rfl,brace_receipt h,stance,_root_.map_sum]; swap; · exact hd
  simp only [brackets, WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply, Complex.ofReal_sum,map_smul,mode,report, smul_eq_mul]; exact Finset.sum_congr rfl fun i _=> Complex.ofReal_mul ..
abbrev More (G:Gauge):Levee G:= Trio G 1 1 0
def εglows (φ:PlaqAxes)(G:Gauge):=∑ a:G.ColorIndex,harmonic (six φ) (endr φ) a* mode (six φ) (endr φ) a
lemma incurred (p:PlaqAxes): V3 G (tile p)-εglows p G∈ More G:=by
  rw [pi3,εglows,← Finset.sum_sub_distrib,More,trio3]; apply Submodule.sum_mem; intro i _; change _ - harp _* _ ∈ _; rw [← mul_sub]; apply Submodule.mul_mem_mul; exact sap (touch_cane 0 _ _ [] _); rw [← wakes]; exact hollow (k₂g (returns p i))
end YM.XSpace.Gland
