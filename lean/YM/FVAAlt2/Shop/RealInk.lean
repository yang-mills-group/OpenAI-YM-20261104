import YM.FVAAlt2.Plus.Menu
import YM.FVAAlt2.Fixed
import YM.Planned.PRIMARY_INTEGRAL_295.Columns
import YM.PertExtension.BareWords
/-!
# Actual stencil realization: every actual section tested as a Lit.launch.
Choices: real basis Spans. The `fieldAt` is the actual Wilson column, not
recovering it from symbol. Holds on ANY period/index/horizon, not just nonwrapping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Lattice Function Finset Filter Topology Wilson Labels Source Source.Drops
open Planned.PrimaryIntegral295.Place
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor
open MS.Cylinder.Lab
open scoped Topology ContDiff
variable {G:Gauge}{d:ℕ}{n:Side}{F:Labels.Frame G d}(S : SectionData F)
local notation "W"=> Spot S.stencil
local notation "M"=> W × Conn G
local notation "D₀"=> Dev S.stencil G
local notation "L"=> (placeEdge (S:=S.stencil))
variable (j:F.Index)
def port : Dev S.stencil G→ℝ:= Complex.re ∘ column S j
abbrev origin : Dot G Cover:= Sew.art (placeEdge (S:=S.stencil)) (port S j)
lemma port_germ : germ (port S j):=Complex.reCLM.contDiff.contDiffAt.comp (f:=column S j) 0 (column_smooth S j).contDiffAt
lemma onPort(x:MS.Native.Chart.City G (Site n)): fieldAt S j 0 (MS.Native.Chart.nation x)= port S j (Sew.pull (Sew.thread (wrap n) L) x):=by
 unfold fieldAt port column slant copy SectionData.places
 simp only [Function.comp_apply]
 apply congr_arg Complex.re; apply S.cylinder_local
 intro p hx he; unfold pore expandAt; rw [dif_pos (show p.1∈ S.stencil∧p.1+step p.2∈S.stencil from ⟨hx,he⟩),add_zero];rfl
lemma doc_co(k:Side): enters k (origin S j)=reads (fieldAt S j 0 ∘ MS.Native.Chart.nation):=by
 rw [origin,Sew.enters_gorge _ _ (port_germ ..)]; exact congr_arg _ (funext (fun x=> (onPort S j x).symm))
lemma invField {H:Hol G}(h:S.Sound H)(x:Site n): MS.Native.Chart.OpenGauge (MS.Native.Chart.drive n) (fieldAt S j x):= by
 intro u U; unfold fieldAt; rw [show MS.Native.Chart.siteGauge _ _ _= gauge (fun x=>(u x)⁻¹) U from ?_,S.placed_invariant h]
 ext1; simp [MS.Native.Chart.siteGauge,Lattice.gauge,MS.Native.Chart.endRail,MS.Native.Chart.drive]
lemma howField (x:Site n):moveLetter x (fieldAt S j 0) = fieldAt S j x:= by
 funext U; unfold fieldAt moveLetter; rw [show U ∘ turnAddress x= translate x U by ext1; unfold translate turnAddress; simp [add_comm]]; simp [S.places_trans]
lemma port_cost(h:Bid.pop S)(k:ℕ)(he:k<(F.grades j).2): iteratedFDeriv ℝ k (port S j) 0=0:= by
 unfold port; change iteratedFDeriv ℝ k (Complex.reCLM ∘ column S j) 0=_
 ext v; rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.reCLM ((column_smooth S j).contDiffAt.of_le (m:=ω) le_top),radials_vanish S h j _ he]; simp; exact le_top
-- direct ink ↔ differential; use rank Order
lemma inkJet {A X:Type}[NormedAddCommGroup X][NormedSpace ℝ X](e:A→X)(f:X→ℝ)(h:germ f)(k:ℕ)(x:Fin k→A): ink e f (List.ofFn x)=(↑(iteratedFDeriv ℝ k f 0 (e ∘ x)):ℂ):=by
 induction k generalizing f with
 | zero=> simp
 | succ k ih=> rw [List.ofFn_succ,ink,ih (layer _ f) (germ_layer h _)]; exact congr_arg Complex.ofReal ( Eq.symm (Eq.trans (DFunLike.congr_arg _ (Fin.cons_self_tail (e ∘ x)).symm) (Analysis.cons_inner (h.of_le le_top) _ _)))

variable {H:Hol G}(h:S.Sound H)(hp:Bid.pop S)
include hp in
lemma lowPort : From (origin S j).val (F.grades j).2:= by
 let f:=ink (Native.priv (Q:=W)) (port S j); let V:= MS.Cylinder.region.symm f
 intro w hw; have ht: Book.model w.length V=0:= by
   apply Subtype.ext; funext x; by_cases he:x.length=w.length
   · change mask w.length f x=0
     rw [enough _ (by rw [he])]; have H:= inkJet (priv (Q:=W) (G:=G)) _ (port_germ S j) x.length x.get; rw [port_cost S j hp _ (by omega)] at H; simpa [f] using H
   exact strange _ (by omega)
 rw [ ← enough w (F:=(origin S j).val) (h:=w.length) rfl,← mask_s (origin S j), show model w.length (origin S j)=Ferry (Sew.knot L) (model w.length V) from (mod_ferry V (Sew.knot L)).symm,ht,map_zero ];rfl
include h in
lemma fieldReal_in (v:CoverConfig G): (( (S.evaluate (Pi.single j 1) v).re:ℝ):ℂ)= S.evaluate (Pi.single j 1) v:=by
 have he: star (Pi.single j 1:F.Coeff)=Pi.single j 1:=by funext i; simp [Pi.single_apply]
 exact Complex.conj_eq_iff_re.mp (Eq.symm (by nth_rw 1 [← he]; exact h.ordinary_real _ _ ))
lemma static (n:Side): germ (fieldAt S j (0:Site n) ∘ MS.Native.Chart.nation):= by
 apply ContDiffAt.congr_of_eventuallyEq (f:= (port S j) ∘ (Sew.pull (Sew.thread (wrap n) L))); swap; exact Eventually.of_forall (onPort (n:=n) S j)
 exact ContDiffAt.comp (f:= Sew.pull (Sew.thread (wrap n) L)) 0 (by rw [map_zero]; exact port_germ S j) ((show ContDiff ℝ ω (Sew.pull (Sew.thread (wrap n) L) (G:=G)) from ContinuousLinearMap.contDiff _).contDiffAt)
include h hp
lemma aura : Studio.Aura (origin S j) (F.grades j).2:= ⟨ lowPort S j hp,Native.Tune_port L (port S j) (port_germ S j),fun k=> ⟨ fieldAt S j 0, invField S j h (0:Site k), static S j k, doc_co S j k⟩⟩
lemma field_ok(x:Site n): AtomCert x (origin S j) (F.grades j).2 (fieldAt S j x):=by rw [← howField]; exact AtomCert.on_aura _ _ (aura S j h hp) _ (invField S j h (0:Site n)) (static S j n) (doc_co S j n)
end YM.FVAAlt2.Shop
