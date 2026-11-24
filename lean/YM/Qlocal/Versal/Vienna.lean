import YM.Qlocal.Versal.Dunes
import YM.Qlocal.Quipu.Brew
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local
/-! Concrete renderer costs.Has room for future α and ownership ages.

 Emission as transparent short+long (rank-zero included for now, representing
 their `global` predecessors uses mask spill separately). Support of all group
 and flag history regions chosen up front for authored terms, can use force
 alignment to/from masked state. No claim λ multilinearity beyond track (this is REAL). Older `a` discrepancy pose paid per-source not rough union.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6 AnalyticBridge
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i z w:ℕ} {c:Side} {d t a v u C φ g:ℝ}{R:Census V}
-- Ξ.Real. Complete actual Regular entry WITH ownership and cost all pins on all fields, also for court OR other chosen scope. no pay mask spills.
structure PayR (p:BudgetPoint)(H:Support c)(v:ℝ)(f:Config G c→ℝ):Prop where
  safe : 0 ≤ v
  genuine : p.Regular H f
  statement (i:Site c)(h:i∈H): p.supBounds i H f v
namespace PayR
variable {f g:Config G c→ℝ}{p:BudgetPoint}{H:Support c}
protected lemma sub (hf: PayR p H v f) (hg:PayR p H t g): PayR p H (v+t) (f-g):= ⟨add_nonneg hf.safe hg.safe,CouplingShape.reg_sub hf.genuine hg.genuine,fun i hi=> CouplingShape.sup_sub hf.genuine hg.genuine (hf.statement i hi) (hg.statement i hi)⟩
lemma z_m (u:ℝ)(h: PayR p H v f):PayR p H (|u| *v) (u • f):= ⟨mul_nonneg (abs_nonneg u) h.safe,CouplingShape.reg_scale _ h.genuine,fun i hi=> CouplingShape.sup_scale _ (h.statement i hi)⟩
protected lemma add (hf: PayR p H v f) (hg:PayR p H t g):PayR p H (v+t) (f+g):= by
 simpa using hf.sub (hg.z_m (-1)) -- needs explicit simp
lemma Nether (p:BudgetPoint)(G:Gauge)(H:Support c): PayR p H (|0|:ℝ) (0:Config G c→ℝ):= ⟨abs_nonneg _,CouplingShape.reg_const _,fun i hi=>CouplingShape.sup_const _⟩
protected lemma zero (p:BudgetPoint)(G:Gauge)(H:Support c): PayR p H 0 (0:Config G c→ℝ):= abs_zero (α:=ℝ) ▸ Nether p G H -- check
lemma bound (h:PayR p H v f) (hX:H.Nonempty) (W:Config G c): ‖masked p.threshold H f W‖ ≤ v:= by obtain ⟨i,hi⟩:=hX; exact CouplingShape.mask_cost (h.statement i hi) W
lemma enlarge (h:PayR p H v f) (he:v≤u):PayR p H u f:= ⟨h.safe.trans he,h.genuine,fun i hi=> CouplingShape.sup_larger (h.statement i hi) he⟩
lemma sum (u:Finset ι)(s:ι→ Config G c→ℝ)(L:ι→ℝ)(he:∀ i∈u,PayR p H (L i) (s i)): PayR p H (∑ i∈u,L i) (∑ i∈u,s i):= by
 induction u using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact PayR.zero ..
 | insert i u hi ih=> rw [sum_insert hi,sum_insert hi]; exact (he i (mem_insert_self ..)).add (ih fun j hj=> he j (mem_insert_of_mem hj))
end PayR
namespace Tale
variable (p:BudgetPoint)(l:Lattice.Order)(s:Senses R)(A:Tale R G) (X:A.Decision)(o:V→Site c)(x:Site c)(W:Config G c)
set_option quotPrecheck false
-- birth criterion.S.Dimension.Ranks.Fit.Path.O.Env.Frame name
local notation "I"=>Fin (A.depth+1)
set_option quotPrecheck false
local notation "J" i=> Fin (Fin.val i +Lagger.dues A.power s.val+1)
variable (i:Fin (A.depth+1))(n:Fin (i.val+Lagger.dues A.power s.val+1))
local notation "A★"=> A.array s i n
local notation "K"=> Sonnet.root s
local notation "S"=> o K
local notation "m"=> A.method
local notation "Ψ"=> A.stampE s i n
local notation "κ"=> A.boom s
local notation "θ"=> p.threshold
/-- predicate for unwrapped and winding, retains field-independent terms; `S=first root` of preset author slot set. -/
noncomputable abbrev short (A:Tale R G)(X:A.Decision)(b:ℕ) : A.Decision := fun s e n i=> X s e n i ∧ (A.array s e n i).momentum ≤ b
noncomputable abbrev long (A:Tale R G)(X:A.Decision)(b:ℕ) : A.Decision := fun s e n i=> X s e n i ∧ b < (A.array s e n i).momentum
protected abbrev court (b:ℕ)(x:Site c):= Lattice.halo b {x}
def Live (o:V→Site c)(s:Senses R)(b:ℕ):= ∀ v ∈ essence s,separation (o (Sonnet.root s)) (o v) ≤ b
noncomputable abbrev termR (g:ℝ): Config G c→ℝ:= (g^A.stampE s i n/(g^A.boom s)) • playing A X o s i n -- param ordering.T
noncomputable def wake (g:ℝ):= ∑ i:I,∑ n:J i,termR s A X o i n g
local notation "C₀"=> Tale.court p.B S
local notation "u!"=>A.short X k
local notation "p₀"=> g^Ψ/g^κ
local notation "P!"=> termR s A u! o i n g
-- ensure ALL analytic ranking rays labelled at `g^(e-r)`
lemma notationW (t:ℝ) : wake s A X o t W= A.markℓ X o s t W / t^A.boom s:= by unfold wake markℓ; simp only [Finset.sum_apply, Finset.sum_div,termR,Pi.smul_apply,smul_eq_mul]; ring_nf; rfl
lemma pole (hp:0<g) : (g^Ψ/g^κ)*θ^n.val = g^i.val*(θ/g)^n.val:= by
 have he: Ψ+n.val=i.val+κ:= by unfold boom stampE; omega
 have hv:0≤θ:= p.threshold_pos.le
 have hP : g^Ψ*g^n.val=g^i.val*g^κ:= by rw [← pow_add,he,pow_add]
 rw [div_pow]; field_simp; grind
lemma alive (q:ℕ)(h:A.short X k s i n q)(hx:(A★ q).stage.Hears o) : Live o s k:= by intro v hv; exact le_trans ((A★ q).radius (Equiv.refl _) _ _ (Vase.marked (s:=s) (Equiv.refl _) o (A★ q) hx v hv)) h.2
lemma thaw (he:¬Live o s k): termR s A u! o i n g=0 := by -- delete unused hq
 rw [termR, show playing A u! o s i n=0 from ?_, smul_zero]; funext U; unfold playing Album.picture Album.realize; change _=(0:ℝ); apply Eq.trans (tsum_congr (g:=fun j:ℕ=>0) ?_) tsum_zero; intro j; unfold Album.readout; rw [if_neg (fun ⟨h,hx⟩=> he (alive s A X o i n j h hx))]; rfl
noncomputable abbrev sky (r k:ℕ)(t:ℝ)(v a:ℝ)(C:ℝ)(b:ℕ):= t * Vase.humid G p.power p.order k r b 1 v a * C
noncomputable def gold (p:BudgetPoint)(G:Gauge)(w k e:ℕ)(v a C g:ℝ):= g^e*(p.threshold/g)^k * Vase.humid G p.power p.order k w p.B 1 v a * C
include l
lemma paid (h:t/p.B≤d)(he:0 ≤ t)(hd:0≤d)(ha:0<a)(hv:0≤v)(ht:(A★).Health (d+a+v) C) (hk:k≤p.B)(hx:0<g) : PayR p (Tale.court p.B (o (Sonnet.root s))) (gold p G A.method n.val i.val t a C g * Real.exp (-(t*coverNumber p.B (C₀)))) (P!) := by
 let j' i' := (u!) s i n i' ∧ (A★ i').stage.Hears o
 have hp(i':ℕ)(h':j' i') : Vase.Carrier l (A★ i') S 1 p.B p.B (C₀):= Vase.verge l (A★ i') S (h'.1.2.trans hk)
 have hh:= Album.chilly l A★ S p j' ht h he hp hv 0 (fun i hi=> Nat.zero_le _) m ha
 rw [Nat.cast_zero,mul_zero,add_zero] at hh; obtain ⟨hh,hx'⟩:= Album.money l A★ S p j' hp hh ht (by linarith)
 have hT:PayR p (C₀) _ _:=⟨(hx' S (halo_subset _ _ (mem_singleton_self S))).1,hh,hx'⟩
 have hy:= hT.z_m (g^Ψ/g^κ); have hy':0≤g^Ψ/g^κ:=by positivity
 rw [abs_of_nonneg hy', ← mul_assoc, ← mul_assoc,← mul_assoc, pole p s A i n hx] at hy; exact hy
end Tale
end YM.Qlocal.Quipu.Sonnet
