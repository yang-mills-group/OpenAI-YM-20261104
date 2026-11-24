import YM.FVAAlt2.First.Leg
import YM.FVAAlt2.First.Homo
import YM.FVAAlt2.Shop.Menus
import YM.SchemeRG11.Roll.Lute
/-! True Pert.Full stencil for real marks, build on its own Ray basis at weight 0. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Native MS.Native.Draft MS.Book MS.Plane MS.Theater MS.Landau MS.Landau.Detect MS.Lifting MS.Tone MS.Momentum
open Pert Pert.Orb MS.Cylinder.Lab Cylinder.Taylor
open SchemeRG11 SchemeRG11.Haze SchemeRG11.Pile SchemeRG11.Sway
open MvPolynomial
open Complex (I)
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius PowerSeries Classical
variable {G: Gauge}{d:ℕ}{F: Frames G}{n:Side}{p q:pLabel G}
local notation "Ω"=> Lane4 G
local notation "Φ"=> Dot G Cover
-- period charts real actual moments, extended from real symbols only
abbrev sensor (o:Site n)(A:Config G n):=(fun p:pLabel G=> aeval (fun i:Key G=> legAt i o A) p)
abbrev sensorMap (o:Site n): pLabel G →ₗ[ℝ] (Config G n→ℝ):= LinearMap.pi (fun U:Config G n=> (aeval (R:=ℝ) (fun i:Key G=> legAt i o U)).toLinearMap)
-- `Signature`
structure Cert (u:Dot G Cover)(p:pLabel G): Prop where
 cost: Tuned u 0
 born (n:Side): Native.Studio.Reads (shown n u) (sensorMap (0:Site n) p)
variable {u v: Dot G Cover}
lemma cert_one : Cert (G:=G) ( Cylinder.piece 1 ) 1:=by
 refine ⟨ ⟨ coin_symm _,by intro i h;cases i; contradiction; rfl, fun i=>by rw [Cylinder.piece]; cases i <;> simp [coin] ⟩, fun n=>?_⟩
 rw [show sensorMap (0:Site n) (1:pLabel G)=(fun _=>1) from funext fun _=> map_one (aeval (fun i:Key G=> _))]; unfold shown transport; rw [coin_settled]; exact ⟨contDiffAt_const, (by change coin (1:ℂ) = Taylor.ink _ (fun _=>1); rw [ink_const, Complex.ofReal_one])⟩
namespace Cert
lemma isCoin (v:ℝ): (MvPolynomial.C v : pLabel G)=v • (1:pLabel G):=by rw [MvPolynomial.smul_eq_C_mul,mul_one]
lemma scalar (c:ℝ)(h:Cert u p): Cert (( c:ℂ ) • u) ( c • p ):= ⟨ h.cost.cash _ (by simp), fun n=> by rw [_root_.map_smul,_root_.map_smul]; exact (h.born n).cash c ⟩
lemma add (h:Cert u p)(k:Cert v q): Cert (u+v) (p+q):= ⟨h.cost.add k.cost, fun n=> by rw [_root_.map_add,_root_.map_add]; exact ⟨(h.born n).born.add (k.born n).born, (by rw [Submodule.coe_add, (h.born n).home, (k.born n).home,reads,reads]; exact ( ink_add _ (h.born n).born (k.born n).born ).symm)⟩ ⟩
lemma mul (h:Cert u p)(k:Cert v q): Cert (couple DotFlip u v) (p*q):= by
 refine ⟨h.cost.pair k.cost,fun n=>?_⟩; rw [show sensorMap (0:Site n) (p*q)=sensorMap 0 p * sensorMap 0 q from funext fun x=> (aeval (fun i:Key G=> legAt i 0 x)).map_mul p q, show shown n (couple _ _ _)=_ from transport_comes (wrap n) (F:=u) (H:=v) ]; exact (h.born n).pair (k.born n) -- maybe argument ambiguity
lemma unique (H:Cert u p)(h:Cert v p): u=v:= (enterEq ..).mp (Eventually.of_forall fun n=> (H.born n).home.trans (h.born n).home.symm )
lemma leg (i:Key G): Cert (origin i) (X i) := ⟨price_phase i,fun n=>by rw [show sensorMap (0:Site n) (X i)=legAt i (0:Site n) from funext fun x=>aeval_X (fun j=> legAt j _ x) i]; apply roots_co⟩
end Cert
lemma cement (p:pLabel G): ∃ u:Φ, Cert u p:=by
 induction p using MvPolynomial.induction_on with
 | C c=> rw [Cert.isCoin]; exact ⟨_, cert_one.scalar c⟩
 | add p q hp hq=> exact ⟨_,hp.choose_spec.add hq.choose_spec⟩
 | mul_X p i hp=>exact ⟨_,hp.choose_spec.mul (Cert.leg i)⟩
def resident (p:pLabel G): Dot G Cover := (cement p).choose
lemma parallels (p:pLabel G): Cert (resident p) p:= (cement p).choose_spec
-- Linear w.r.t. REAL POL before pack-level pigment
lemma formed_mul (p q:pLabel G): resident (p*q)= couple DotFlip (resident p) (resident q):= (parallels _).unique ((parallels p).mul (parallels q))
lemma formed_add (p q:pLabel G): resident (p+q)= resident p+resident q:= (parallels _).unique ((parallels p).add (parallels q))
lemma formed_smul (c:ℝ)(p:pLabel G): resident (c • p)=( c:ℂ ) • resident p:= (parallels _).unique ((parallels p).scalar c)
lemma formed_one : resident (1:pLabel G)= Cylinder.piece 1:= (parallels _).unique cert_one
lemma formed_C (c:ℝ): resident (G:=G) (MvPolynomial.C c)= (c:ℂ) • (Cylinder.piece 1):=by rw [Cert.isCoin, formed_smul,formed_one]
lemma formed_X(i:Key G): resident ( X i )=origin i:= (parallels _).unique (Cert.leg i)
lemma formed_zero : resident (0:pLabel G)=0:=by rw [← C_0,formed_C]; simp
lemma formed_low(h:p.IsHomogeneous d): From (resident p).val (d:ℤ):= by
 refine paradigm (fun _=>1) (fun j:ℕ=> fun p:pLabel G=> From (resident p).val j) h (fun x=>?_) (fun x=>?_) (fun v i f hu hp=>?_) (fun v p q hu hx hv hk=>?_)
 · exact fun _ _=> by omega
 · rw [formed_zero]; exact fun _ _=> rfl
 · rw [formed_mul,formed_X]; exact (first i).pair hp
 rw [formed_add]; exact hv.add hk
end YM.FVAAlt2.Pairing
