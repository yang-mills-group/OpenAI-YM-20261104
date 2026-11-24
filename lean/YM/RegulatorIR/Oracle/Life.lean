import YM.RegulatorIR.Oracle.Fitness

/-! Pack constructor prior to RG08. Endings by ellipt. Bulk defined in t
using flags' actual branch prior to UV. TAccounts statement printed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Step YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping Uniform
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {X:Type} {M:X→ℕ} {n:Page M→Side} {K:KernelChoices} {k p:ℕ}{γ:ℝ}
namespace Circuit
variable (S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G) (t:Page M→Binding.Scale)
local notation "A"=>S.dialect Y G Z t
local notation "T"=>S.lane Y G Z t
-- field spend options. parameter t tracked per-family; Space positivity selected. extend TOP log gauges.

def mural (w:X): Face ℤ→ Orders (Foot G):= (plain_exists (t (Page.opening M w)) G).choose
lemma serene (w): Prim.Plane (t (Page.opening M w)) G (mural G t w):=(plain_exists _ _).choose_spec

def padV (w:X): Orders (Foot G):= many (mural G t w)

def recordQ (w:X):Orders (Binding.Book G (n (Page.opening M w))):=fun i j=> Deck.deckSum (S.opened G (Page.opening M w)) (padV G t w i j)
include S
lemma fitsV (w):Vacuum (padV G t w):=(Prim.ark _ (S.dual _) (S.comet (Page.opening M w)) (serene G t w)).grammar
lemma ratesQ (w):Vacuum (recordQ S G t w):=(Prim.ark _ (S.dual _) (S.comet (Page.opening M w)) (serene G t w)).format

def payroll : (A).Accounts := {
 bulk:= Halo.seriesC (X:=fun _=>Orders (Foot G)) (padV G t) (fun j=>(S.devices Y G Z t j).pure)
 orb:= Halo.seriesC (X:=fun p=>Orders (Binding.Book G (n p))) (recordQ S G t) (fun j=>(S.devices Y G Z t j).common)
 step_v:=fun w=> (Halo.laterC w).symm
 step_o:=fun w=>(Halo.laterC w).symm
 top_v:=fun w=> S.fitsV G t w
 top_o:=fun w=> S.ratesQ G t w }
lemma follows : (T).Follows (payroll S Y G Z t):= fun w=>⟨_,serene G t w,rfl, rfl⟩
variable (L:Meter X)(V:S.Credit Y G Z t L k p)
local notation "Q"=> S.payroll Y G Z t
lemma gifted : ∀ w i j,(S.lane Y G Z t|>.pulses w) i j=(S.lane Y G Z t|>.pulses w) j i := fun w i j=> (congr_fun (congr_fun (t_warm (S.pactP w) K G _ (S.honored Y w.prev).card (Z _)) j) i)
-- LOCK α.P pricing.Aux continuation. RG08 supplies

def Vacancy (p k:ℕ):Prop:=∀ i≤p,∀ j, Workday (coverL M L) ((A).census.cone k) fun p=> (Q).bulk p i j
include V
lemma habits (H: Vacancy S Y G Z t L p k): SchemeBeam T Q (S.pushP Y G) (S.takeP Y G) L (S.leadA Y G k) p k:=⟨S.follows Y G Z t,paid_full S Y G Z t L V, ⟨fun _=>rfl⟩,payingB S Y G Z t L V,⟨H,fun _ _ _ _=> Halo.helium T Q (S.follows Y G Z t) _ _ _ ⟩,S.gifted Y G Z t⟩

omit V
lemma happens (D:Choice M)(hL:∀ w,S.l (D.choose w)=1)(h:0<γ)(he:γ≤1)(H:Uniform.Poly (flapL M L) (fun w=> ENNReal.ofReal ((S.sizeL w).val:ℝ)))(hv:∀ p:Flap M,S.leadA Y G k p ≤ ENNReal.ofReal ((((S.sizeL p).val:ℝ)^γ)⁻¹)) : Lantern A D L (S.leadA Y G k) γ:=by
 have hx (i:Flap M) : (A).shift i=((S.sizeL i).val:ℝ):=by rw [shift]; change S.l i.next/S.l i.prev= _; rw [S.width_s i]; field_simp [(S.l_p i.prev).ne']
 refine { ref_mesh:= hL, gleams:=h,small:=he,scale:=?_,cold:=?_,side:=?_ }
 · simp_rw [hx]; exact H
 · simp_rw [hx]; exact hv
 intro w;let i:=D.choose w;rw [← show S.l i*(n i).val=(A).P w from S.comet i, show S.l i= _ from hL w, one_mul]; exact_mod_cast (n i).property
lemma enduras (c:ℕ)(h:∀ w,(n (Page.finallyW M w)).val≤c)(hc : Uniform.Poly L (fun w=> ENNReal.ofReal (Y.receipt.η (S.J (Page.finallyW M w)))⁻¹)) : Reel.Endings T L:=by
 refine { periods:=⟨c,h⟩, pay:=?_,symw:=?_,ellipt:=⟨(fun w=>Y.receipt.η (S.J (Page.finallyW M w))),fun _=> Y.receipt.eta_pos _,hc,?_⟩ }
 · intro w; have he:= S.honored Y (Page.finallyW M w); exact crust_f G _ he.card.stripP.2.1 he.card.pos.le he.card.paid
 · intro w i; have he:= S.honored Y i; exact gears_A G (S.dual i) (S.comet i) (crustA G _) (tune_s G _ he.card (fun n=>he.symmetryP n G))
 intro w i; have he:= S.honored Y i; exact crust_s _ he.card.stripP.2.1 he.card.pos.le he.card.paid (he.card.floorP _)
end Circuit
end YM.RegulatorIR.Oracle
