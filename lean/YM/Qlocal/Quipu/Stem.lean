import YM.Qlocal.Quipu.Lotus
import YM.Qlocal.Quipu.Zora
import YM.Qlocal.Quipu.Amber
import YM.Qlocal.Quipu.Lagger
/-!
 Canon-mark syllabus. Displacement basis keeps source roots without translation quotient, each term invariant. Pole price in extra curve, weighted at true path sector. `Gen` applies also at AUXILIARY periods by same uncropped packet. Spatial prices permit conversion to Orientation appointment in this model. Rendering wind errors, higher Gauge commutators and held text require separate ledger on actual masked representation. Real sector; can probe at least any finite product of independent tests by sending through weights before transport.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {V:Type}[DecidableEq V]{ι:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
local notation "Ω"=> G.Color
abbrev Senses (R:Census V):= Multi.Hot R
variable (s:Senses R)
def essence (s:Senses R):= s.val.val
-- root fixed deterministic
protected def root : V:= Classical.choose s.property
@[simp] theorem ownership : Sonnet.root s∈ essence s:= Classical.choose_spec s.property
structure Bay (s:Senses R) where
   pursue : V → Cover
   starts : pursue (Sonnet.root s)=0
   rest (v : V)(h:v∉essence s): pursue v=0
namespace Bay
variable {s:Senses R}(A:Bay s)
def tariff (A:Bay s):ℕ:= ∑ i∈ essence s,size (A.pursue i)
abbrev Hears {n:Side}(o:V→Site n):= ∀ i∈ essence s,o i=bent (o (Sonnet.root s)) (A.pursue i)
abbrev site (o:Lattice.Order)(A:Bay s): Finset Cover:= (essence s).biUnion fun i=> aperture (route 0 (A.pursue i) o)
instance : Inhabited (Bay s):= ⟨⟨fun _=>0,rfl,fun _ _=>rfl⟩⟩ -- replace
lemma stable (i: V)(hi:i∈ essence s) : size (A.pursue i)≤ A.tariff:= Finset.single_le_sum (f:=fun i=> size (A.pursue i)) (fun i _=> Nat.zero_le _) hi
end Bay
-- Actor.Can hold ANY paid closed w (slotWalk, axial-closed, masked comparisons later)
abbrev Ranks (G:Gauge)(n:ℕ):= Stationary.Ink G n
variable {s} (p:Lattice.Order)(o:V→Site c)
open Zora
structure Vase (s:Senses R)(G:Gauge)(n:ℕ) where
    stage : Bay s
    ink : Ranks G n→ℝ
    maps : Fin n→ Wand G
    tan : Fin n→ Bool -- Θ t or raw curvature
    legal : ink ∈ paints G n
namespace Vase
-- *prices for comparison apply at ℓ before painter t-ratio.*
variable (A:Vase s G n)(x: Site c)(V':Config G c)
abbrev reach (A:Vase s G n):= ∑ i:Fin n, ((A.maps i).range+(A.maps i).tour.length)
def momentum (A:Vase s G n):= A.reach+A.stage.tariff
def sizeC (A:Vase s G n):= ∑ i:Ranks G n, |A.ink i|
lemma nn_size :0≤ A.sizeC:= by unfold sizeC; positivity
abbrev fare (A:Vase s G n)(a:ℝ):= A.sizeC*Real.exp (a*A.momentum)
lemma sizes (he:0≤a): A.sizeC ≤ A.fare a:= le_mul_of_one_le_right A.nn_size (Real.one_le_exp (by positivity))
def coin (p:Lattice.Order) (A: Vase s G n) := (insert 0 (Bay.site p A.stage))∪(Finset.univ.biUnion fun i:Fin n=> aperture (A.maps i).tour)
def cone (p:Lattice.Order) (A: Vase s G n)(x:Site c):= (A.coin p).image (bent x) -- dot p A
local notation "ℓ"=>A.cone p x -- scope reader ν.S
abbrev amend (G:Gauge)(k:ℕ)(t:Bool) : G.El→ G.Color:= if t then theta G k ∘ G.curvature else G.curvature
-- Decompression via theta k only when explicitly requested. Gauge and evaluation for all Links.
lemma marked (h:Bay.Hears A.stage o)(u:V)(hh:u∈essence s): o u∈ A.cone p (o (Sonnet.root s)):=by
 let x₀:=o (Sonnet.root s); let w:=A.stage.pursue u; have ht:w∈coin p A:= Finset.mem_union_left _ (Finset.mem_insert_of_mem (mem_biUnion.mpr ⟨u,hh,List.mem_toFinset.mpr ((show stop 0 (route 0 w p)= w from route_end ..) ▸ done 0 (route 0 w p))⟩)) -- route casts
 exact (h u hh).symm ▸ Finset.mem_image_of_mem (bent x₀) ht -- bug u=root cast.A
lemma belongs (j:Fin n) : Crown (A.maps j).tour x⊆ A.cone p x:=by
 apply Finset.image_mono; intro i hi; exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, mem_univ _,hi⟩)
def flavor (V:CoverConfig G) (i:Fin n):= amend G k (A.tan i) (travel V 0 (A.maps i).tour)
def draw (V:CoverConfig G):= ∑ i:Ranks G n, A.ink i * ∏ j:Fin n,flavor (k:=k) A V j (i j) -- explicit k field
abbrev read (A:Vase s G n)(x:Site c)(k:ℕ)(V':Config G c) := draw (k:=k) A (expandAt x V')
lemma globe (k:ℕ) : read A x k V'= ∑ i: Ink G n,A.ink i * Noon.bump i (fun j=> amend G k (A.tan j) (travel V' x (A.maps j).tour)) := by unfold read draw Noon.bump flavor; simp_rw [travel_at,map_zero,zero_add]
lemma legitimate (k:ℕ) : GaugeInvariant (read A x k):= by
 intro t U; simp_rw [globe, travel_gauge, Wand.basis_z]
 have he(t:Bool)(u v:G.El): amend G k t (u*v*u⁻¹)=G.adjoint u (amend G k t v):= by unfold amend; split; simp_rw [Function.comp_apply,G.curvature_conjugate,theta_moves]; simp_rw [G.curvature_conjugate]
 simp_rw [he]; exact A.legal (t x) (fun j=> amend G k (A.tan j) _)
lemma located (k:ℕ) : LocalOn ↑(A.cone p x) (read A x k):= by
 intro U V h; have hh i: travel U x (A.maps i).tour= travel V x (A.maps i).tour:= by apply travel_local; apply agrees_mono h; intro t ht; exact A.belongs p x i ((found_crown _ x).symm ▸ List.mem_toFinset.mpr ht) -- args inspect
 rw [globe,globe]; simp_rw [hh]
-- model may be field-independent rank=0 with ℓ full.Location.Sum.
noncomputable def vac (s:Senses R)(G:Gauge)(n:ℕ): Vase s G n:=⟨default,fun _=>0, fun _=>default, fun _=>false,(paints G n).zero_mem⟩
instance : Inhabited (Vase s G n):=⟨vac s G n⟩
lemma amen (G:Gauge)(i:Bool)(k:ℕ) : Continuous (amend G k i):= by
  have hc: Continuous G.curvature:= G.projectColor.continuous_of_finiteDimensional.comp ((G.continuous_mat.sub (G.continuous_mat.comp continuous_inv)).const_smul (1/2:ℝ)); unfold amend; split; exact (theta_cont G k).continuous.comp hc; exact hc
@[fun_prop] lemma cont_ (k:ℕ) : Continuous (read A (x:Site c) k):= by
 rw [funext (fun V=> A.globe x V k)]; apply continuous_finsetSum _; intro i _; unfold Noon.bump; apply continuous_const.mul; exact continuous_finsetProd _ fun j _=> (EuclideanSpace.proj _).continuous.comp ((amen _ _ _).comp (continuous_travel ..))
end Vase
end YM.Qlocal.Quipu.Sonnet
