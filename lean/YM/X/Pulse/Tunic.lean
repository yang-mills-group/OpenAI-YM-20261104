import YM.X.Pulse.Sphere
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
variable (Y:T→ℕ)
def stand (e:ℝ) (d:ℕ): Module.End ℂ (E d):= scalePolDiff F (fun b=>(e:ℂ)^b.1) d -- F implicit incl?
def huddle (i:(F.level d).Index) : E d:= let a:= F.level d; let u:= (up F (a.bound i)) (Gravity.billet (q:=q) S (useWord S i) w k); (Complex.ofReal ((epsilon q k)^(- (Bare.wt F i:ℤ)))) • stand (F:=F) (epsilon q k) d u -- incl q k issues
-- placeholders include
lemma seal_zoom {e:ℝ}(h:0<e) (x:E d): Bare.held S e⁻¹ d k (physicalLabel F d (stand e d x))=raw S d k (physicalLabel F d x):= by
    rw [stand,scalePol_physical,held]; simp only [LinearMap.comp_apply]; apply congr_arg; apply (F.level d).coords.injective; funext i; unfold upoff; rw [scalePol_eq,scalePol_eq,← mul_assoc,Complex.ofReal_inv,← mul_pow,inv_mul_cancel₀,one_pow,one_mul]; exact_mod_cast h.ne'
lemma helm (i:(F.level d).Index): (held S E₀⁻¹ d 0) (physicalLabel F d (huddle (q:=q) (k:=k) S w i))=rebate q w k (useWord S i) S:= by
    let B:= (up F ((F.level d).bound i)); rw [huddle,map_smul,map_smul,seal_zoom S (epsilon_pos q k),up,physical_inclusion F (scheme_filters F)]; unfold raw;rw [common_scale]; change (_:ℂ) • ((raw _ _ 0) _)=_; unfold rebate; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)];rfl
-- natural lift across equal grades only needed low filt
lemma entry_book (i:(F.level d).Index) (j:ℕ) (h:(useWord S i).d≤j) (hx:j≤d): huddle (q:=q) (k:=k) S w i∈ lower F j d:= by
    let b:=stand (F:=F) (epsilon q k) (useWord S i).d (Gravity.billet (q:=q) S (useWord S i) w k); unfold huddle; apply Submodule.smul_mem; rw [up_pre F hx]; refine ⟨(up F h) b,?_⟩; rw [up_mul,show (up F _) b=_ from scalePol_up F (fun g=>(epsilon q k:ℂ)^g.1) _ _];rfl
-- Drive compensation over all upper Labels first
-- include q k in scope below. choose d explicit bind
def advance (d:ℕ): Labels.Label G d→ₗ[ℂ] E d:= (F.level d).basis.constr ℂ (huddle (q:=q) (k:=k) (d:=d) S w)
def away (d:ℕ): Module.End ℂ (E d):= advance (q:=q) (k:=k) S w d ∘ₗ physicalLabel F d
variable {m:ℕ}
lemma advance_eq (i:(F.level d).Index): advance (k:=k) (q:=q) S w d ((F.level d).basis i)= huddle (k:=k) (q:=q) S w i:= Module.Basis.constr_basis ..
lemma stove : away (q:=q) (k:=k) S w d ((Model F).unit d)=0:= by
    rw [away,LinearMap.comp_apply,physical_unit,← (F.level d).starts_unit,advance_eq,huddle,engine_unit S w]; erw [map_zero (up F ((F.level d).bound 0)),map_zero (stand (F:=F) _ d),smul_zero]

lemma stayed (x:E d) (h:m<d) (hp:x∈lower F m d) : away (q:=q) (k:=k) S w d x∈ lower F m d:= by
    rw [up_pre F h.le] at hp; obtain ⟨p,rfl⟩:=hp; rw [away,LinearMap.comp_apply,up,physical_inclusion F (scheme_filters F),← (F.level m).basis.sum_repr (physicalLabel F m p),map_sum, map_sum]; apply Submodule.sum_mem; intro i _; rw [map_smul,map_smul]; apply Submodule.smul_mem; obtain ⟨u,he⟩:= Horizon.reference_rises F h.le i; rw [he,advance_eq]; have heq : useWord S i=useWord S u:= re_born F S.H S.S S.hS S.hP (congr_arg (fun t:Labels.Label G d=>t.val) he); apply entry_book S w u m _ h.le; rw [← heq, use_weight]; exact (F.level m).bound i
end YM.PositionX.Pulse
