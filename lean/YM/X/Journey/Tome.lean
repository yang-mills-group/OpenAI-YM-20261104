import YM.X.Journey.Lip
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
open Pert.Position Maxwell Maxwell.Free Bare Function Pert.RawLabels
variable {F:Labels.Frames G}(S:Bare.Shop F) (w:Floor R)
local notation "E"=> Pert.Position.E F
local notation "A"=> F.level d
local notation "L"=> Labels.Label G d
local notation "E₀"=> epsilon q k
open Screens Beamer CellsInt
variable {m:ℕ}(a:Beam q)(ha:∀i,a i∈origins q i)(hq:1<q.val)
local notation "Fℕ"=>(atTop:Filter ℕ)
include ha
lemma at_origin: Away a (-a):= by
    have he:= stares _ (placement q a ha); rwa [show stared (q:=q) (positiveLift a)=a from ?_] at he; ext i x; change (Int.cast (R:=Per (side q i)) (↑((a i x).val):ℤ))= a i x; simp
omit ha
lemma on_neighbor (p:Fielding.Walk){x:E4}(h:plot q p x): Near a (fun i=> wrap (side q i) (p i) +a i):= by
    let b(i):= wrap (side q i) (p i)+a i; apply Near.circ; refine (show Charged q (raysD b a) from ⟨1, Ripe.eventual (B:= 4*(‖x‖+1)) ?_⟩); filter_upwards [h.norm.eventually (ge_mem_nhds (lt_add_one ‖x‖))] with i hi; unfold raysD; rw [Real.norm_of_nonneg (by positivity)]; let z:=spot (epsilon q i); unfold separation b; rw [add_sub_cancel_right]; refine le_trans (Nat.cast_le.mpr (wrap_rotate ..)) ?_;
    have hw : (epsilon q i)*(street (p i):ℝ)≤4*(‖x‖+1):= le_trans (street_cost _) (mul_le_mul_of_nonneg_left hi (by norm_num)); rw [ticket,zpow_one]; rw [eps_eq,inv_mul_eq_div,div_le_iff₀ (amp_pos ..)] at hw; exact hw
local notation "O" i=> Grid.offsets q m i
variable (v:∀i:ℕ,Grid.offsets q m i)(z:Points m)(r:ℝ)(hr:R<r) (hv:Tendsto (fun i=> Grid.sample q i (v i)) atTop (𝓝 z))(g:Fin m→ Pert.Position.E F d)(hg:G.Simple)
-- tilted physical neighborhoods (ε-independent when r chosen)
abbrev Region (m:ℕ)(r:ℝ): Set (Points m):= {p| Porch.Apart Finset.univ p.ofLp r}
def kin (s:Fin m→ Site n)(e:ℝ)(b:Buffer F d): alma (Pert.Position.E F d) m:= outerK S e s d 1-passV (bufferL F b) (outerK S e s d 0)
def teamK (S:Shop F)(i:ℕ)(a:Site (side q i))(v:Grid.offsets q m i)(d:ℕ)(w:Floor R) := kin S (fun j=>v j+a) (epsilon q i) (barter (q:=q) (k:=i) (d:=d) S w)
include ha hg hq hv hr
lemma walks_visit (h:z∈Region m r): Released (fun i=> teamK S i (a i) (v i) d w g):= by
    let y(j:Fin m)(i:ℕ):= lift (v i j); let t(j:Fin m):Beam q:=fun i=> postal y (a i) i j; have hp(j:Fin m):plot q (y j) (z j):= Grid.sample_each hq hv j; -- args
    let B:=fun i:ℕ=>bufferL F (barter (d:=d) (q:=q) (k:=i) S w); obtain ⟨c,hc⟩:= Barter_balance (m:=m) S w r hq hr y z.ofLp hp h a g; refine ⟨c,?_⟩; let he:=courtesy S B t a (at_origin a ha) (fun i=>on_neighbor a (y i) (hp i)) hq hg (fun i=> Barter_charge S w hq i) g; let f(i:ℕ)(b:ℕ):= outerK S (epsilon q i) (fun j=>t j i) d b; let hh:= he.goes hq; have hw:= hh.add hc; rw [zero_add] at hw; apply hw.congr; intro k; change (((f k 1-passV (B k) (f k 0)) g) - ?w)+ ?w=_; rw [sub_add_cancel]; change (f k 1-passV (B k) (f k 0)) g=_; unfold f t postal stock y; simp_rw [wrap_lift];rfl
end YM.PositionX.Pulse
