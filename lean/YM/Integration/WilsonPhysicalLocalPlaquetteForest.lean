import YM.Integration.WilsonPhysicalLocalPlaquetteRoutes
import YM.Integration.WilsonPhysicalForestAnchor
import YM.Integration.WilsonAxialWindow

/-! Price the actual forest-gauged fine bond. Its forest path may turn and
backtrack. Only the two block roots use coordinate routes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPhysicalLocalPlaquetteForest
open Lattice RG Wilson Tree
open WilsonPhysicalAnchoredGauge WilsonPhysicalForestAnchor
open scoped Classical BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f}

/-- Actual box needed for the auxiliary, based plaquette filling. -/
def radius (D L:ℕ):ℕ:=D+4*L+1

/-- Number of charged single-link bounds in the two arms and their bond. -/
def lanes (D L:ℕ):ℕ:=2*(4*L+4*(2*(D+4*L)+1))+1

def area (D L:ℕ):ℝ:=(lanes D L:ℝ)*(4*(radius D L:ℝ)*Fintype.card PlaqAxes)

theorem fits (D L n:ℕ) (support:4*D<n) (block:16*L+4≤n):2*(radius D L)<n:=by
  unfold radius;omega

private theorem arm (F:Forest S.ratio) (o x:Site f) (D:ℕ) (dx:separation o x≤D)
    (V:Config G f) {K:ℝ} (pos:0≤K)
    (cap:∀i:Edge (Site f),separation o i.1<radius D S.ratio.count.val→G.chord (V i)≤K):
    G.chord (travel V x ((roads F o).arm x))≤((4*S.ratio.count.val+
      4*(2*(D+4*S.ratio.count.val)+1):ℕ):ℝ)*K:=by
  let L:=S.ratio.count.val
  have first:=(F.hike_lower x).trans (F.bound x)
  change (F.hike x).length≤4*L at first
  have dist:=Push.Uniform.stop_length x (F.hike x)
  rw [F.hike_root] at dist
  change separation x (foot S x)≤(F.hike x).length at dist
  have bound (v:Site f) (hv:v∈visits x (F.hike x)):separation o v<radius D L:=by
    have step:=WilsonPhysicalAnchoredPaths.visited x v (F.hike x) hv
    have add:=separation_triangle o x v
    unfold radius;omega
  let V':Config G f:=fun i=>if separation o i.1<radius D L then V i else 1
  have agree:travel V x (F.hike x)=travel V' x (F.hike x):=by
    apply travel_local;intro i h _;simp only [V',if_pos (bound _ h)]
  have uniform (i:Edge (Site f)):G.chord (V' i)≤K:=by
    by_cases h:separation o i.1<radius D L
    · simpa only [V',if_pos h] using cap i h
    · simpa only [V',if_neg h,G.chord_one] using pos
  have head:=Next.Fluctuations.travel_chord V' (F.hike x) x K uniform
  rw [←agree] at head
  have footD:separation o (foot S x)≤D+4*L:=
    (separation_triangle o x _).trans (Nat.add_le_add dx (dist.trans first))
  have tail:=WilsonPhysicalLocalPlaquetteRoutes.centered o (foot S x) (D+4*L) footD V K pos
    (fun i hi=>cap i (by change separation o i.1<D+4*L+1;omega))
  change G.chord (travel V x (F.hike x ++ _))≤_
  rw [travel_append,F.hike_root]
  have skip:G.chord (travel V x (F.hike x))≤(4*L:ℕ)*K:=head.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast first) pos)
  exact (G.chord_triangle _ _).trans ((add_le_add skip tail).trans_eq (by
    change _=((4*L+4*(2*(D+4*L)+1):ℕ):ℝ)*K
    push_cast; ring))

private theorem based_price (A:Roads f) (V:Config G f) (e:Edge (Site f)) (a b:ℝ)
    (first:G.chord (travel V e.1 (A.arm e.1))≤a) (bond:G.chord (V e)≤b)
    (last:G.chord (travel V (e.1+step e.2) (A.arm (e.1+step e.2)))≤a):
    G.chord (based A V e)≤2*a+b:=by
  let left:=travel V e.1 (A.arm e.1)
  let right:=travel V (e.1+step e.2) (A.arm (e.1+step e.2))
  have h1:=G.chord_triangle left⁻¹ (V e)
  rw [G.chord_inv] at h1
  have h2:=G.chord_triangle (left⁻¹*V e) right
  have eq:based A V e=left⁻¹*V e*right:=by
    simp only [based,Lattice.gauge,transport,inv_inv,left,right]
  rw [eq];change G.chord left≤a at first;change G.chord right≤a at last
  linarith only [h1,h2,first,bond,last]

private theorem rotate_chord (h:G.El) (U:Config G f) (e:Edge (Site f)):
    G.chord (rotate h U e)=G.chord (U e):=G.chord_conj _ _

theorem field (F:Forest S.ratio) (o:Site f) (D:ℕ) (period:2*radius D S.ratio.count.val<f.val)
    (U:Config G f) {τ:ℝ} (hτ:0≤τ)
    (cold:∀z∈WilsonAxialWindow.cells o (radius D S.ratio.count.val),G.chord (faceValue U z)≤τ)
    (h:G.El) (e:Edge (Site f)) (base:separation o e.1≤D) (next:separation o (e.1+step e.2)≤D):
    G.chord (rotate h (based (roads F o) U) e)≤area D S.ratio.count.val*τ:=by
  let L:=S.ratio.count.val
  let r:=radius D L
  let K:ℝ:=(4*(r:ℝ)*Fintype.card PlaqAxes)*τ
  let φ:=WilsonAxialWindow.frame 1 o U
  let V:=gauge φ U
  have pos:0≤K:=by dsimp [K];positivity
  have cap (i:Edge (Site f)) (hi:separation o i.1<r):G.chord (V i)≤K:=
    WilsonAxialWindow.bound 1 o U r period i hi hτ cold
  have left:=arm (S:=S) F o e.1 D base V pos cap
  have right:=arm (S:=S) F o (e.1+step e.2) D next V pos cap
  have bond:=cap e (by dsimp [r,radius];omega)
  have buy:=based_price (roads (S:=S) F o) V e _ K left bond right
  have eq:=congrArg (fun Z:Config G f=>G.chord (Z e)) (covariance (roads (S:=S) F o) φ U)
  change G.chord (based (roads F o) V e)=G.chord (rotate _ (based (roads F o) U) e) at eq
  rw [rotate_chord] at eq
  rw [rotate_chord,←eq]
  apply buy.trans_eq
  change 2*(((4*L+4*(2*(D+4*L)+1):ℕ):ℝ)*K)+K=area D L*τ
  unfold area lanes K;dsimp only [r];push_cast;ring

end YM.Integration.WilsonPhysicalLocalPlaquetteForest
